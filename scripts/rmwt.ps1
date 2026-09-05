# Remove a worktree made by mkwt.ps1, junctions first so nothing follows them.
#
#   pwsh -File scripts/rmwt.ps1 -Name kryeig [-DeleteBranch]

param(
  [Parameter(Mandatory = $true)][string]$Name,
  [switch]$DeleteBranch
)

$ErrorActionPreference = "Stop"

$root = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$wtRoot = (Resolve-Path (Join-Path $root "..")).Path
$wt = Join-Path (Join-Path $wtRoot "numlib-wt") $Name

if (Test-Path $wt) {
  # `rmdir` on a junction removes the link, not the target; Remove-Item -Recurse would follow it.
  foreach ($link in @("$wt\.lake\packages", "$wt\tools\tracker\.lake")) {
    if (Test-Path $link) { cmd /c rmdir "$link" | Out-Null }
  }
  Remove-Item -Recurse -Force $wt
}

git -C $root worktree prune
if ($DeleteBranch) { git -C $root branch -D "agent/$Name" }
