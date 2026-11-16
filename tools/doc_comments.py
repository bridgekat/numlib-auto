#!/usr/bin/env python3
"""Rewrite Lean doc comments without touching code.

Subcommands:

  dump FILE [--lines A-B] [--moddoc]
      Print FILE with line numbers. Proof bodies of theorems are elided, and long
      bodies of definitions are truncated. Planned declarations are marked.
      With --lines, print that range in full. With --moddoc, print only the module
      doc comment.

  apply FILE DOCFILE
      Apply the doc comment entries of DOCFILE to FILE. The entries are keyed by
      line numbers of FILE as it is on disk (the numbers that `dump` prints).
      The text is wrapped at 100 columns. The command fails without writing if
      the code of FILE would change.

  check [--base REF] [FILE ...]
      Compare each FILE with its version at REF (default HEAD): the code must be
      identical after comments are removed. Then report style problems in the
      comments. With no FILE, check every Lean file that differs from REF.

Format of DOCFILE (see notes in `prompts/generated/documentation.md` for content):

  @@ doc N      doc comment `/-- ... -/` for the declaration, field or constructor
                at line N. N is the line of the existing `/--`, or the first line
                of the declaration if there is no doc comment yet.
  @@ mod N      module-level comment `/-! ... -/`. N is the line of an existing
                `/-!` (replace it), or a code line (insert a new one before it).
  @@ del N      delete the `/--` or `/-!` comment that starts at line N.

The lines after a header, up to the next header, are the Markdown text of the
comment, without the comment delimiters.
"""
import argparse
import re
import subprocess
import sys
import tomllib
from pathlib import Path

WIDTH = 100
ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Lexer: split a Lean source into code, comments and strings.
# ---------------------------------------------------------------------------

IDENT_TAIL = re.compile(r"[A-Za-z0-9_'!?.ª-￿)\]}]")
CHAR_LIT = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


def lex(src):
    """Return a list of (kind, start, end); kind is one of
    'code', 'line', 'doc', 'mod', 'block', 'string'."""
    segs = []
    i, n, code_start = 0, len(src), 0

    def flush(upto):
        if upto > code_start:
            segs.append(("code", code_start, upto))

    while i < n:
        c = src[i]
        if c == "-" and src.startswith("--", i):
            flush(i)
            j = src.find("\n", i)
            j = n if j < 0 else j
            segs.append(("line", i, j))
            i = code_start = j
        elif c == "/" and src.startswith("/-", i):
            flush(i)
            kind = "doc" if src.startswith("/--", i) else "mod" if src.startswith("/-!", i) else "block"
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if depth:
                raise ValueError("unterminated block comment")
            segs.append((kind, i, j))
            i = code_start = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = min(j + 1, n)
        elif c == "'":
            m = None if (i > 0 and IDENT_TAIL.match(src[i - 1])) else CHAR_LIT.match(src, i)
            i = m.end() if m else i + 1
        elif c == "«":
            j = src.find("»", i)
            i = n if j < 0 else j + 1
        else:
            i += 1
    flush(n)
    return segs


def code_lines(src):
    """The code of `src`: comments removed, trailing space removed, blank lines dropped."""
    out, pos = [], 0
    for kind, a, b in lex(src):
        if kind != "code":
            out.append(src[pos:a])
            pos = b
    out.append(src[pos:])
    return [ln.rstrip() for ln in "".join(out).split("\n") if ln.strip()]


class Source:
    """A Lean file with per-line comment information (lines are 1-based)."""

    def __init__(self, text):
        self.text = text
        self.lines = text.split("\n")
        starts = [0]
        for ln in self.lines:
            starts.append(starts[-1] + len(ln) + 1)
        self.starts = starts
        self.segs = lex(text)
        n = len(self.lines)
        # comment_at[i]: (kind, first_line, last_line) if a block comment starts at the
        # first non-blank character of line i.  inside[i]: line i starts inside a block comment.
        self.comment_at = {}
        self.inside = [False] * (n + 2)
        self.codeonly = [None] * (n + 2)
        import bisect
        pieces, pos = [], 0
        for kind, a, b in self.segs:
            if kind == "code":
                continue
            pieces.append(text[pos:a])
            pieces.append("\n" * text.count("\n", a, b))
            pos = b
            if kind == "line":
                continue
            la = bisect.bisect_right(starts, a)
            lb = bisect.bisect_right(starts, b - 1)
            if text[starts[la - 1]:a].strip() == "":
                self.comment_at[la] = (kind, la, lb)
            for k in range(la + 1, lb + 1):
                self.inside[k] = True
        pieces.append(text[pos:])
        co = "".join(pieces).split("\n")
        for k in range(1, n + 1):
            self.codeonly[k] = co[k - 1]

    def is_code_line(self, k):
        return 1 <= k <= len(self.lines) and not self.inside[k] and self.codeonly[k].strip() != ""


# ---------------------------------------------------------------------------
# Declarations and planned ids.
# ---------------------------------------------------------------------------

MODS = r"(?:(?:private|protected|nonrec|noncomputable|unsafe|partial|scoped|local|public|meta)\s+|@\[[^\]]*\]\s*)*"
DECL = re.compile(r"^(\s*)" + MODS + r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|"
                  r"axiom|example|irreducible_def|alias)\b\s*([^\s:({\[⦃]*)")
PROOF_KINDS = {"theorem", "lemma", "example"}
OPEN, CLOSE = "([{⟨⟦⦃", ")]}⟩⟧⦄"


def planned_ids(path):
    rel = Path(path).resolve().relative_to(ROOT)
    plan = ROOT / "plans" / rel.with_suffix(".toml")
    if not plan.exists():
        return set()
    try:
        data = tomllib.loads(plan.read_text(encoding="utf-8"))
    except Exception:
        return set()
    ns = data.get("namespace", "")
    out = set()
    for node in data.get("node", []):
        i = node.get("id", "")
        if i.startswith("_root_."):
            out.add(i[len("_root_."):])
        else:
            out.add(f"{ns}.{i}" if ns else i)
    return out


def scan_decls(src):
    """Yield dicts for column-0 declarations: line, kind, name, full name, extent end."""
    n = len(src.lines)
    stack, decls = [], []
    col0 = [k for k in range(1, n + 1)
            if not src.inside[k] and src.lines[k - 1][:1].strip() != ""]
    nxt = {}
    for a, b in zip(col0, col0[1:] + [n + 1]):
        nxt[a] = b
    for k in col0:
        line = src.codeonly[k]
        if not line.strip():
            continue
        m = re.match(r"^(?:noncomputable\s+|public\s+)*(namespace|section|mutual)\b\s*(\S*)", line)
        if m:
            stack.append((m.group(1), m.group(2)))
            continue
        if re.match(r"^end\b", line):
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if not m:
            continue
        kind, name = m.group(2), m.group(3)
        ns = ".".join(s[1] for s in stack if s[0] == "namespace" and s[1])
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        elif name:
            full = f"{ns}.{name}" if ns else name
        else:
            full = ""
        end = nxt[k] - 1
        while end > k and src.lines[end - 1].strip() == "":
            end -= 1
        decls.append(dict(line=k, kind=kind, name=name, full=full, end=end,
                          private=bool(re.match(r"^(@\[[^\]]*\]\s*)*private\b", line))))
    return decls


def body_start(src, d):
    """(line, column) just after the depth-0 `:=` of a declaration, or None."""
    depth = 0
    for k in range(d["line"], d["end"] + 1):
        if src.inside[k]:
            continue
        s = src.codeonly[k]
        j = 0
        while j < len(s):
            c = s[j]
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0 and s.startswith(":=", j):
                return k, j + 2
            elif depth == 0 and k > d["line"] and re.match(r"\s+\|\s", s) and j == 0:
                return k, 0
            j += 1
    return None


# ---------------------------------------------------------------------------
# dump
# ---------------------------------------------------------------------------

DEF_CAP = 30


def cmd_dump(args):
    text = Path(args.file).read_text(encoding="utf-8")
    src = Source(text)
    n = len(src.lines)
    if args.moddoc:
        for k in sorted(src.comment_at):
            kind, a, b = src.comment_at[k]
            if kind == "mod":
                print(f"# {args.file}")
                print("\n".join(src.lines[a - 1:b]))
                return
        print(f"# {args.file}: no module doc comment")
        return
    lo, hi = 1, n
    if args.lines:
        lo, hi = (int(x) for x in args.lines.split("-"))
    planned = planned_ids(args.file)
    decls = scan_decls(src)
    skip = {}      # line -> (last skipped line, message)
    marks = {}
    found = set()
    for d in decls:
        if d["full"] in planned:
            marks[d["line"]] = "P"
            found.add(d["full"])
        bs = body_start(src, d)
        if not bs:
            continue
        k, col = bs
        if d["kind"] in PROOF_KINDS:
            if col == 0:
                skip[k] = (d["end"], "proof elided")
            elif d["end"] > k or src.codeonly[k][col:].strip() not in ("", "by"):
                # keep the text up to `:=` on line k, elide the rest
                skip[k] = (d["end"], "proof elided", col)
        elif d["kind"] in ("def", "abbrev", "instance", "opaque", "irreducible_def"):
            if d["end"] - k > DEF_CAP:
                skip[k + DEF_CAP] = (d["end"], "body truncated")
    if args.lines:
        skip = {}  # an explicit range is printed in full
    missing = sorted(planned - found)
    print(f"# {args.file}  ({n} lines). 'P>' marks a planned declaration: full doc comment required.")
    if planned:
        print(f"# planned declarations in this module: {len(planned)}"
              + (f"; not located by the scanner: {', '.join(missing)}" if missing else ""))
    k = lo
    while k <= hi:
        tag = "P>" if k in marks else "  "
        if k in skip:
            item = skip[k]
            last = item[0]
            if len(item) == 3:
                print(f"{k:5d}{tag}{src.lines[k - 1][:item[2]]} ⋯ [{item[1]}, lines {k}–{last}]")
            else:
                print(f"       ⋯ [{item[1]}, lines {k}–{last}]")
            k = last + 1
            continue
        print(f"{k:5d}{tag}{src.lines[k - 1]}")
        k += 1


# ---------------------------------------------------------------------------
# Wrapping of Markdown text.
# ---------------------------------------------------------------------------

NBSP = "\x00"
LIST_ITEM = re.compile(r"^(\s*)([*+-]|\d+[.)])\s+")
DANGEROUS = re.compile(r"^([*+\-=>#|]+|\d+[.)])$")
SPAN = re.compile(r"(`+)(?:(?!\1).|\n)+?\1|(?<![\\$])\$(?!\$)[^$\n]+?(?<!\\)\$(?!\$)")


def protect(s):
    """Make spaces inside short code spans and inline formulas non-breaking."""
    def rep(m):
        t = m.group(0)
        return t.replace(" ", NBSP) if len(t) <= 48 else t
    return SPAN.sub(rep, s)


def wrap(text, width, first_prefix="", rest_prefix=""):
    toks = protect(" ".join(text.split())).split(" ")
    merged = []
    for t in toks:
        if merged and DANGEROUS.match(t.replace(NBSP, " ")):
            merged[-1] += NBSP + t
        else:
            merged.append(t)
    out, cur = [], first_prefix
    empty = True
    for t in merged:
        if empty:
            cur += t
            empty = False
        elif len(cur) + 1 + len(t) <= width:
            cur += " " + t
        else:
            out.append(cur)
            cur = rest_prefix + t
    out.append(cur)
    return [ln.replace(NBSP, " ") for ln in out]


def format_markdown(text, width):
    """Wrap Markdown `text` to `width`. Returns a list of lines."""
    out, para = [], []
    para_first, para_rest = "", ""

    def flush():
        nonlocal para
        if para:
            out.extend(wrap(" ".join(para), width, para_first, para_rest))
            para = []

    lines = text.split("\n")
    i = 0
    while i < len(lines):
        ln = lines[i].rstrip()
        st = ln.strip()
        if st.startswith("```"):
            flush()
            out.append(ln)
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("```"):
                out.append(lines[i].rstrip())
                i += 1
            if i < len(lines):
                out.append(lines[i].rstrip())
            i += 1
            continue
        if st.startswith("$$"):
            flush()
            block = [ln]
            if not (len(st) > 2 and st.endswith("$$") and st.count("$$") >= 2):
                i += 1
                while i < len(lines):
                    block.append(lines[i].rstrip())
                    if "$$" in lines[i]:
                        break
                    i += 1
            risky = any(re.match(r"^\s*([-+*>#]|\d+[.)])(\s|$)", b) for b in block[1:])
            if all(len(b) <= width for b in block) and not risky:
                out.extend(block)
            else:
                ind = re.match(r"\s*", block[0]).group(0)
                out.extend(wrap(" ".join(b.strip() for b in block), width, ind, ind + "  "))
            i += 1
            continue
        if st == "":
            flush()
            out.append("")
        elif st.startswith("#") or st.startswith("|"):
            flush()
            out.append(ln)
        else:
            m = LIST_ITEM.match(ln)
            if m:
                flush()
                para_first = m.group(0)
                para_rest = " " * len(m.group(0))
                para = [ln[len(m.group(0)):]]
            elif para:
                para.append(st)
            else:
                ind = re.match(r"\s*", ln).group(0) if out and out[-1].startswith(" ") and ln.startswith(" ") else ""
                para_first = para_rest = ind
                para = [st]
        i += 1
    flush()
    while out and out[-1] == "":
        out.pop()
    while out and out[0] == "":
        out.pop(0)
    res = []
    for ln in out:
        if ln == "" and res and res[-1] == "":
            continue
        res.append(ln)
    return res


def render_doc(text, indent):
    lines = format_markdown(text, WIDTH - len(indent) - 4)
    if not lines:
        raise ValueError("empty doc comment")
    lines[0] = "/-- " + lines[0]
    last = lines[-1]
    special = last.lstrip().startswith(("$$", "|", "```")) or last.rstrip().endswith("$$")
    if not special and len(indent) + len(last) + 3 <= WIDTH:
        lines[-1] = last + " -/"
    else:
        lines.append("-/")
    return [(indent + ln) if ln else "" for ln in lines]


def render_mod(text, indent):
    lines = format_markdown(text, WIDTH - len(indent))
    if not lines:
        raise ValueError("empty module comment")
    if len(lines) == 1 and len(indent) + len(lines[0]) + 7 <= WIDTH:
        return [indent + "/-! " + lines[0] + " -/"]
    return [indent + "/-!"] + [(indent + ln) if ln else "" for ln in lines] + [indent + "-/"]


# ---------------------------------------------------------------------------
# apply
# ---------------------------------------------------------------------------

NOTATION = re.compile(r"^\s*" + MODS + r"(notation|infix[lr]?|prefix|postfix|macro|syntax|elab|macro_rules|"
                      r"declare_syntax_cat|initialize|add_decl_doc)\b")
CONTAINER = {"structure", "class", "inductive"}


def insertable(src, N):
    line = src.codeonly[N]
    if re.match(r"^\s*(omit|include|open|set_option|variable|universe|namespace|section|end|attribute)\b", line):
        return False
    if DECL.match(line) or NOTATION.match(line) or re.match(r"^\s*@\[", line):
        return True
    if line[:1].strip() == "":
        for d in scan_decls(src):
            if d["line"] < N <= d["end"]:
                return d["kind"] in CONTAINER and bool(re.match(r"^\s+(\||[A-Za-z_«(\[{])", line))
    return False


HEADER = re.compile(r"^@@\s*(doc|mod|del)\s+(\d+)\s*$")


def parse_docfile(text):
    entries, cur = [], None
    for ln in text.split("\n"):
        m = HEADER.match(ln)
        if m:
            cur = [m.group(1), int(m.group(2)), []]
            entries.append(cur)
        elif ln.startswith("@@"):
            raise ValueError(f"bad header line: {ln!r}")
        elif cur is not None:
            cur[2].append(ln)
        elif ln.strip():
            raise ValueError("text before the first '@@' header")
    return [(k, n, "\n".join(body).strip("\n")) for k, n, body in entries]


def apply_entries(text, entries):
    src = Source(text)
    lines = src.lines
    n = len(lines)
    edits = []  # (first_line, last_line_exclusive, new_lines)  -- replace lines[first-1:last-1]
    errors = []
    for kind, N, body in entries:
        where = f"@@ {kind} {N}"
        if not (1 <= N <= n):
            errors.append(f"{where}: line out of range")
            continue
        if "-/" in body or "/-" in body:
            errors.append(f"{where}: the text contains '-/' or '/-', which would break the comment")
            continue
        com = src.comment_at.get(N)
        indent = re.match(r"\s*", lines[N - 1]).group(0)
        try:
            if kind == "del":
                if not com or com[0] not in ("doc", "mod"):
                    errors.append(f"{where}: no '/--' or '/-!' comment starts at this line")
                    continue
                a, b = com[1], com[2] + 1
                if b <= n and lines[b - 1].strip() == "" and (a == 1 or lines[a - 2].strip() == ""):
                    b += 1
                edits.append((a, b, []))
            elif kind == "doc":
                if not body.strip():
                    errors.append(f"{where}: empty text (use '@@ del' to delete a comment)")
                    continue
                if com and com[0] == "doc":
                    edits.append((com[1], com[2] + 1, render_doc(body, indent)))
                elif src.is_code_line(N) and not com:
                    if not insertable(src, N):
                        errors.append(f"{where}: a new doc comment can go only before a declaration, a structure "
                                      "field or a constructor; this line is not one (for 'omit ... in' or "
                                      "'include ... in', use the line of the declaration after it)")
                        continue
                    k = N
                    while k > 1 and src.is_code_line(k - 1) and re.match(r"^\s*@\[[^\]]*\]\s*$", src.codeonly[k - 1]):
                        k -= 1
                    prev = [c for c in src.comment_at.values() if c[2] == k - 1 and c[0] == "doc"]
                    indent = re.match(r"\s*", lines[k - 1]).group(0)
                    if prev:
                        edits.append((prev[0][1], prev[0][2] + 1, render_doc(body, indent)))
                    else:
                        edits.append((k, k, render_doc(body, indent)))
                else:
                    errors.append(f"{where}: this line is neither the start of a '/--' comment nor a code line")
            else:
                if not body.strip():
                    errors.append(f"{where}: empty text (use '@@ del' to delete a comment)")
                    continue
                if com and com[0] == "mod":
                    edits.append((com[1], com[2] + 1, render_mod(body, indent)))
                elif not src.inside[N] and (not com or com[0] == "doc"):
                    # insert a new block; never between a doc comment and its declaration
                    k = N
                    if not com:
                        while k > 1 and src.is_code_line(k - 1) and \
                                re.match(r"^\s*@\[[^\]]*\]\s*$", src.codeonly[k - 1]):
                            k -= 1
                        prev = [c for c in src.comment_at.values() if c[2] == k - 1 and c[0] == "doc"]
                        if prev:
                            k = prev[0][1]
                    new = render_mod(body, "")
                    if k > 1 and lines[k - 2].strip() != "":
                        new = [""] + new
                    if lines[k - 1].strip() != "":
                        new = new + [""]
                    edits.append((k, k, new))
                else:
                    errors.append(f"{where}: this line is inside a comment or starts a comment that is not '/-!'")
        except ValueError as e:
            errors.append(f"{where}: {e}")
    # order at one line: new '/-!' block, then new '/--' comment, then replacement
    def prio(e):
        a, b, new = e
        return 2 if b > a else (0 if new and new[-1 if new[-1] else -2].lstrip().startswith(("/-!", "-/")) and
                                not any(x.lstrip().startswith("/--") for x in new) else 1)
    edits = sorted(edits, key=lambda e: (e[0], prio(e)))
    for e1, e2 in zip(edits, edits[1:]):
        if e2[0] < e1[1] or (e1[0] == e2[0] and prio(e1) == prio(e2)):
            errors.append(f"two entries target the same comment or line (lines {e1[0]} and {e2[0]})")
    if errors:
        return None, errors
    out = lines[:]
    for a, b, new in reversed(edits):
        out[a - 1:b - 1] = new
    return "\n".join(out), []


def cmd_apply(args):
    path = Path(args.file)
    text = path.read_text(encoding="utf-8")
    try:
        entries = parse_docfile(Path(args.docfile).read_text(encoding="utf-8"))
    except ValueError as e:
        sys.exit(f"error: {e}")
    new, errors = apply_entries(text, entries)
    if errors:
        print("NOT APPLIED. Fix these entries and run again:")
        for e in errors:
            print("  " + e)
        sys.exit(1)
    try:
        same = code_lines(new) == code_lines(text)
    except ValueError as e:
        sys.exit(f"NOT APPLIED: the result does not lex ({e})")
    if not same:
        sys.exit("NOT APPLIED: the code would change. Check that no entry text contains comment delimiters.")
    path.write_text(new, encoding="utf-8")
    print(f"applied {len(entries)} entries to {args.file}; line numbers have changed, dump again before a second apply")
    problems = style_problems(str(path), new)
    report(str(path), problems)


# ---------------------------------------------------------------------------
# check
# ---------------------------------------------------------------------------

H2_ORDER = ["Coverage", "Contents", "Main definitions", "Main results", "Proof outline", "Notation",
            "Conventions", "Implementation notes", "Deviations from the source", "Not formalized"]
FORBIDDEN = [
    (re.compile(r"\b(notes|plans)/"), "refers to a file outside the published library"),
    (re.compile(r"\b[\w/]+\.lean\b"), "refers to a file path; use the module name"),
    (re.compile(r"\b(sub-?agents?|orchestrator|worktree|formalizer agent)\b", re.I), "mentions the work process"),
    (re.compile(r"\b(TODO|FIXME)\b"), "contains a TODO"),
]
MATH_IN_TICKS = re.compile(r"`[^`\n]*(?:\^\{|_\{|\\[a-zA-Z]{2,})[^`\n]*`")


def style_problems(path, text):
    probs = []
    src = Source(text)
    lines = src.lines
    mods = [c for _, c in sorted(src.comment_at.items()) if c[0] == "mod"]
    if not mods:
        probs.append((1, "no module doc comment"))
    else:
        kind, a, b = mods[0]
        body = lines[a - 1:b]
        if not any(l.startswith("# ") for l in body[:3]):
            probs.append((a, "the module doc comment must start with a '# Title' line"))
        seen = []
        for off, l in enumerate(body):
            if l.startswith("## "):
                h = l[3:].strip()
                if h not in H2_ORDER:
                    probs.append((a + off, f"heading '## {h}' is not one of the fixed headings"))
                else:
                    if seen and H2_ORDER.index(h) < H2_ORDER.index(seen[-1]):
                        probs.append((a + off, f"heading '## {h}' is out of order"))
                    seen.append(h)
        for kind, a2, b2 in mods[1:]:
            for off, l in enumerate(lines[a2 - 1:b2]):
                if re.match(r"^(/-!\s*)?#{1,2} ", l):
                    probs.append((a2 + off, "a sectioning comment must use a '###' heading"))
    for k, (kind, a, b) in sorted(src.comment_at.items()):
        if kind not in ("doc", "mod"):
            continue
        body = "\n".join(lines[a - 1:b])
        for off, l in enumerate(lines[a - 1:b]):
            if len(l) > WIDTH:
                probs.append((a + off, f"line longer than {WIDTH} characters"))
        if len(re.findall(r"(?<!\\)\$", body)) % 2:
            probs.append((a, "odd number of '$' in this comment"))
        for rx, msg in FORBIDDEN:
            m = rx.search(body)
            if m:
                probs.append((a, f"{msg}: '{m.group(0)}'"))
        m = MATH_IN_TICKS.search(body)
        if m:
            probs.append((a, f"mathematical notation in backticks; use LaTeX: {m.group(0)[:60]}"))
    decls = scan_decls(src)
    doc_ends = {c[2] for c in src.comment_at.values() if c[0] == "doc"}
    for d in decls:
        if d["private"] or d["kind"] in ("instance", "example", "alias"):
            continue
        k = d["line"]
        while k > 1 and src.is_code_line(k - 1) and re.match(r"^\s*@\[[^\]]*\]\s*$", src.codeonly[k - 1]):
            k -= 1
        if (k - 1) not in doc_ends:
            probs.append((d["line"], f"public {d['kind']} '{d['name']}' has no doc comment"))
    return probs


def report(path, problems):
    for line, msg in sorted(problems):
        print(f"{path}:{line}: {msg}")
    if not problems:
        print(f"{path}: no style problems")


def cmd_check(args):
    base = args.base
    files = args.files
    if not files:
        out = subprocess.run(["git", "diff", "--name-only", base, "--", "*.lean"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout
        files = [f for f in out.split("\n") if f.strip()]
    bad = 0
    for f in files:
        p = (ROOT / f) if not Path(f).is_absolute() else Path(f)
        rel = p.resolve().relative_to(ROOT)
        new = p.read_text(encoding="utf-8")
        r = subprocess.run(["git", "show", f"{base}:{rel}"], cwd=ROOT, capture_output=True)
        if r.returncode != 0:
            print(f"{rel}: not present at {base}")
            continue
        old = r.stdout.decode("utf-8")
        try:
            same = code_lines(old) == code_lines(new)
        except ValueError as e:
            same = False
            print(f"{rel}: does not lex ({e})")
        if not same:
            bad += 1
            print(f"{rel}: CODE CHANGED relative to {base}")
        probs = style_problems(str(rel), new)
        if probs or not args.quiet:
            report(str(rel), probs)
    print(f"checked {len(files)} files; {bad} with code changes")
    sys.exit(1 if bad else 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("dump")
    d.add_argument("file")
    d.add_argument("--lines")
    d.add_argument("--moddoc", action="store_true")
    d.set_defaults(fn=cmd_dump)
    a = sub.add_parser("apply")
    a.add_argument("file")
    a.add_argument("docfile")
    a.set_defaults(fn=cmd_apply)
    c = sub.add_parser("check")
    c.add_argument("--base", default="HEAD")
    c.add_argument("--quiet", action="store_true")
    c.add_argument("files", nargs="*")
    c.set_defaults(fn=cmd_check)
    args = ap.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
