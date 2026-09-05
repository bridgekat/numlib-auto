# Create a git worktree for a sub-agent that shares Mathlib's oleans with the main checkout.
#
#   pwsh scripts/mkwt.ps1 -Name wt-foo -Branch agent/foo
#
# The worktree gets `.lake/packages` as a junction to the main checkout (read-only in practice)
# and a copy of `.lake/build`, so `lake build Numlib` is incremental instead of a 3-minute
# cold build.  Remove it again with `scripts/rmwt.ps1`, never with `rm -rf`: a recursive delete
# follows the junction and takes Mathlib's oleans with it.
param(
  [Parameter(Mandatory = $true)][string]$Name,
  [Parameter(Mandatory = $true)][string]$Branch
)

$ErrorActionPreference = 'Stop'
$main = Split-Path -Parent $PSScriptRoot
$root = Split-Path -Parent $main
$dest = Join-Path $root $Name

if (Test-Path $dest) { throw "$dest already exists; remove it with scripts/rmwt.ps1 first" }

git -C $main worktree add $dest -b $Branch
if ($LASTEXITCODE -ne 0) { throw "git worktree add failed" }
New-Item -ItemType Directory -Path (Join-Path $dest '.lake') -Force | Out-Null
New-Item -ItemType Junction -Path (Join-Path $dest '.lake\packages') `
  -Target (Join-Path $main '.lake\packages') | Out-Null
Copy-Item (Join-Path $main '.lake\build') (Join-Path $dest '.lake\build') -Recurse
Write-Output $dest
