$ErrorActionPreference = 'Stop'
$projectRoot = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
$toolchain = (Get-Content -LiteralPath (Join-Path $projectRoot 'lean-toolchain')).Trim()
$toolchainFolder = $toolchain.Replace('/', '--').Replace(':', '---')
$profileFolder = [Environment]::GetFolderPath('UserProfile')
$compiler = Join-Path $profileFolder ".elan/toolchains/$toolchainFolder/bin/lean.exe"
if (-not (Test-Path -LiteralPath $compiler)) { throw "Compiler not found: $compiler" }
$packagePaths = Get-ChildItem -LiteralPath (Join-Path $projectRoot '.lake/packages') -Directory | ForEach-Object { Join-Path $_.FullName '.lake/build/lib/lean' }
$oldLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = (@($PSScriptRoot) + @($packagePaths)) -join ';'
$logPath = Join-Path $PSScriptRoot 'verification.txt'
try {
    $version = & $compiler --version
    @('Lean verification', "Toolchain: $toolchain", $version, 'Source SHA256:', (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'Exam2025.lean') -Algorithm SHA256).Hash, '') | Set-Content -LiteralPath $logPath -Encoding utf8
    $result = @(& $compiler -o (Join-Path $PSScriptRoot 'Exam2025.olean') (Join-Path $PSScriptRoot 'Exam2025.lean') 2>&1)
    $compileCode = $LASTEXITCODE
    $result | Add-Content -LiteralPath $logPath -Encoding utf8
    "Compile exit code: $compileCode" | Add-Content -LiteralPath $logPath -Encoding utf8
    if ($compileCode -ne 0) { $result | Write-Output; throw 'Lean compilation failed' }
    $audit = @(& $compiler (Join-Path $PSScriptRoot 'Audit.lean') 2>&1)
    $auditCode = $LASTEXITCODE
    $audit | Set-Content -LiteralPath (Join-Path $PSScriptRoot 'axioms.txt') -Encoding utf8
    "Axiom audit exit code: $auditCode" | Add-Content -LiteralPath $logPath -Encoding utf8
    if ($auditCode -ne 0) { $audit | Write-Output; throw 'Lean axiom audit failed' }
    if (($audit -join "`n") -match 'sorryAx') { throw 'Unexpected sorryAx dependency' }
    'No sorryAx dependency in any declared theorem.' | Add-Content -LiteralPath $logPath -Encoding utf8
    Get-Content -LiteralPath $logPath
} finally {
    $env:LEAN_PATH = $oldLeanPath
}
