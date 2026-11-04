param()
$ErrorActionPreference = 'Stop'
$labRoot = $PSScriptRoot
$pythonExe = Join-Path $labRoot '.venv\Scripts\python.exe'
$leanExe = Join-Path $env:USERPROFILE '.elan\bin\lean.exe'
if (-not (Test-Path -LiteralPath $pythonExe)) { throw 'Create .venv and install requirements.txt first.' }
if (-not (Test-Path -LiteralPath $leanExe)) { throw 'Install the pinned Lean toolchain with elan first.' }
$previousLocation = Get-Location
$previousLeanPath = $env:LEAN_PATH
$previousUtf8 = $env:PYTHONUTF8
$previousTemp = $env:TEMP
$previousTmp = $env:TMP
try {
    Set-Location -LiteralPath $labRoot
    $env:LEAN_PATH = $labRoot
    $env:PYTHONUTF8 = '1'
    $testTemp = Join-Path $labRoot '.verification-tmp'
    New-Item -ItemType Directory -Path $testTemp -Force | Out-Null
    $env:TEMP = $testTemp
    $env:TMP = $testTemp
    & $pythonExe -m unittest discover -s tests -v
    if ($LASTEXITCODE -ne 0) { throw 'Python tests failed.' }
    $sources = @('SATSearch.lean','CircuitBounds.lean','CircuitCoverage.lean','CircuitCounting.lean','CircuitSemantics.lean','HardFunction.lean','frontier\LexCounterexample.lean','frontier\AntiChecker.lean','frontier\AntiCheckerRepair.lean','frontier\ExplicitSchedule.lean','frontier\SampleInterpolation.lean','frontier\ParityTeaching.lean','frontier\DependencyBound.lean','frontier\CertificateBlowup.lean','frontier\MCSPScope.lean','frontier\FirstGateExtension.lean','frontier\CircuitRewiring.lean','frontier\GraphHoles.lean','frontier\OptimalSupport.lean','frontier\SparseMonomial.lean','frontier\BooleanMobius.lean','frontier\SparseCertificateBound.lean','frontier\SubsetZeta.lean','frontier\FiniteDimension.lean','frontier\DiagonalWidth.lean','frontier\CoordinateChange.lean','frontier\IsotropicDimension.lean','frontier\TriangularDimension.lean')
    foreach ($source in $sources) {
        $compiled = [IO.Path]::ChangeExtension($source,'.olean')
        & $leanExe -o $compiled $source
        if ($LASTEXITCODE -ne 0) { throw "Lean failed: $source" }
    }
    Write-Output "All tests and $($sources.Count) research Lean files passed. No API calls were made."
} finally {
    $env:LEAN_PATH = $previousLeanPath
    $env:PYTHONUTF8 = $previousUtf8
    $env:TEMP = $previousTemp
    $env:TMP = $previousTmp
    Set-Location -LiteralPath $previousLocation
}
