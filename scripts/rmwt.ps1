# Remove a worktree created by scripts/mkwt.ps1.
#
#   pwsh scripts/rmwt.ps1 -Name wt-foo [-Branch agent/foo]
#
# The `.lake/packages` junction is unlinked with `rmdir` before anything recursive runs:
# `Remove-Item -Recurse` and `git worktree remove` both follow it, which would delete the main
# checkout's Mathlib oleans.
param(
  [Parameter(Mandatory = $true)][string]$Name,
  [string]$Branch
)

$ErrorActionPreference = 'Stop'
$main = Split-Path -Parent $PSScriptRoot
$root = Split-Path -Parent $main
$dest = Join-Path $root $Name

if (-not (Test-Path $dest)) { throw "$dest does not exist" }
$junction = Join-Path $dest '.lake\packages'
if (Test-Path $junction) { cmd /c rmdir "`"$junction`"" }
if (Get-ChildItem $dest -Recurse -Attributes ReparsePoint -ErrorAction SilentlyContinue) {
  throw "$dest still contains a reparse point; refusing to delete"
}
git -C $main worktree remove $dest --force
git -C $main worktree prune
if ($Branch) { git -C $main branch -D $Branch }
