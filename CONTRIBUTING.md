# Contributing

To formalize a textbook or paper, the user can instruct general-purpose LLM agents (e.g. Codex, Claude Code) to start by reading [`main.md`](prompts/main.md).

Example prompt:

```text
Formalize all numbered definitions and propositions the given textbook (already converted to Markdown via OCR, which may contain transcription errors) into this repository. Follow instructions in prompts/main.md.
```

You may also set this as a "goal" (instructing the agent to repeatedly check for completion and resume if incomplete).
