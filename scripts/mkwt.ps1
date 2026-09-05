# Make a cheap git worktree for a sub-agent.
#
#   pwsh -File scripts/mkwt.ps1 -Name kryeig
#
# Creates ../numlib-wt/<Name> on a new branch `agent/<Name>` off HEAD, junctions its
# `.lake/packages` and its `tools/tracker` to the main checkout's (so Mathlib and the tracker
# binary are shared, never re-downloaded and never rebuilt), and copies the project's own
# `.lake/build` so the worktree starts warm: `lake build` in it is a no-op until a file changes.
#
# Never run `lake update` in a worktree: the packages are shared with every other worktree.

param(
  [Parameter(Mandatory = $true)][string]$Name,
  [string]$Rev = "HEAD"
)

$ErrorActionPreference = "Stop"

$root = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$wtRoot = (Resolve-Path (Join-Path $root "..")).Path
$wt = Join-Path (Join-Path $wtRoot "numlib-wt") $Name

if (Test-Path $wt) { throw "worktree $wt already exists" }

git -C $root worktree add -b "agent/$Name" $wt $Rev
if ($LASTEXITCODE -ne 0) { throw "git worktree add failed" }

New-Item -ItemType Directory -Force -Path (Join-Path $wt ".lake") | Out-Null
cmd /c mklink /J "$wt\.lake\packages" "$root\.lake\packages" | Out-Null

# tools/tracker is a submodule, and a worktree does not populate it. Check it out for real --
# junctioning the main checkout's copy instead leaves a `.git` file pointing outside the worktree,
# which makes every `git status` in it fatal -- and share only its build directory, since no agent
# edits the tracker.
git -C $wt submodule update --init tools/tracker
if ($LASTEXITCODE -ne 0) { throw "git submodule update failed" }
Remove-Item -Recurse -Force (Join-Path $wt "tools\tracker\.lake") -ErrorAction SilentlyContinue
cmd /c mklink /J "$wt\tools\tracker\.lake" "$root\tools\tracker\.lake" | Out-Null

# Start warm.
robocopy "$root\.lake\build" "$wt\.lake\build" /E /NFL /NDL /NJH /NJS /nc /ns /np | Out-Null
if ($LASTEXITCODE -ge 8) { throw "robocopy failed with $LASTEXITCODE" }

Write-Output $wt
