[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet('Start','Status','Stop','Validate')]
    [string]$Action,
    [switch]$Simulate,
    [ValidateRange(1,120)]
    [int]$SimulateSeconds=60
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$script:LabRoot=(Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..\..')).Path
$script:TeamRoot=(Resolve-Path -LiteralPath $PSScriptRoot).Path
$script:PythonPath=Join-Path $script:LabRoot '.venv\Scripts\python.exe'
$script:QueuePath=Join-Path $script:TeamRoot 'research_queue.json'
$script:Module='continuation.team.controller'

function Get-OptionalProperty {
    param($Object,[string]$Name)
    if ($null -eq $Object) { return $null }
    $property=$Object.PSObject.Properties[$Name]
    if ($null -eq $property) { return $null }
    return $property.Value
}

function Display-Text {
    param($Value,[int]$Limit=200)
    if ($null -eq $Value) { return '(not reported)' }
    $text=([string]$Value -replace '[\x00-\x1f\x7f-\x9f]',' ' -replace '\s+',' ').Trim()
    if ($text.Length -gt $Limit) { return $text.Substring(0,$Limit)+'...' }
    return $text
}

function Invoke-TeamController {
    param([string[]]$ControllerArguments)
    $lines=@(& $script:PythonPath -B -X utf8 -m $script:Module @ControllerArguments)
    $nativeCode=$LASTEXITCODE
    $joined=$lines -join "`n"
    try { $data=$joined | ConvertFrom-Json }
    catch { throw 'Controller output was not readable JSON. No automatic retry was made.' }
    if ($nativeCode -ne 0) {
        $kind=Display-Text (Get-OptionalProperty $data 'error_type')
        throw "Controller refused the operation ($kind). Inspect STATUS; no automatic retry or STOP reset was made."
    }
    return $data
}

function Get-ReviewedRuntime {
    $runtime=Invoke-TeamController -ControllerArguments @('runtime')
    $configPath=Join-Path $script:LabRoot '.venv\pyvenv.cfg'
    $configured=@(Get-Content -LiteralPath $configPath -Encoding UTF8 | Where-Object { $_ -cmatch '^executable\s*=\s*(.+)$' })
    if ($configured.Count -ne 1) { throw 'The project virtual environment does not identify exactly one native Python executable.' }
    $expectedPython=([string]$configured[0] -creplace '^executable\s*=\s*','').Trim()
    $native=Get-OptionalProperty $runtime 'python_executable'
    $bootstrap=Get-OptionalProperty $runtime 'bootstrap'
    $cwd=Get-OptionalProperty $runtime 'cwd'
    $expectedBootstrap=Join-Path $script:TeamRoot 'runtime.py'
    foreach($pair in @(@($native,$expectedPython),@($bootstrap,$expectedBootstrap),@($cwd,$script:LabRoot))) {
        if (($pair[0] -isnot [string]) -or -not [IO.Path]::IsPathRooted($pair[0]) -or [IO.Path]::GetFullPath($pair[0]) -ine [IO.Path]::GetFullPath($pair[1])) { throw 'Runtime metadata did not match the fixed project runtime paths.' }
    }
    if (-not (Test-Path -LiteralPath $native -PathType Leaf) -or -not (Test-Path -LiteralPath $bootstrap -PathType Leaf)) { throw 'The reviewed native Python runtime or project bootstrap is missing.' }
    $prefix=@(Get-OptionalProperty $runtime 'argument_prefix')
    $expectedPrefix=@('-I','-S','-B','-X','utf8',$expectedBootstrap)
    if ($prefix.Count -ne $expectedPrefix.Count) { throw 'Runtime argument prefix is not the reviewed isolated bootstrap.' }
    for($index=0;$index -lt $expectedPrefix.Count;$index++) {
        if ($prefix[$index] -cne $expectedPrefix[$index]) { throw 'Runtime argument prefix is not the reviewed isolated bootstrap.' }
    }
    $remove=@(Get-OptionalProperty $runtime 'remove_environment')
    $expectedRemove=@('__PYVENV_LAUNCHER__','PYTHONHOME','PYTHONPATH')
    if ($remove.Count -ne $expectedRemove.Count) { throw 'Runtime environment cleanup is not the reviewed fixed list.' }
    for($index=0;$index -lt $expectedRemove.Count;$index++) {
        if ($remove[$index] -cne $expectedRemove[$index]) { throw 'Runtime environment cleanup is not the reviewed fixed list.' }
    }
    return $runtime
}

function Show-TeamStatus {
    param($State)
    Write-Host ('Run: '+(Display-Text (Get-OptionalProperty $State 'run_id')))
    Write-Host ('Phase: '+(Display-Text (Get-OptionalProperty $State 'phase')))
    Write-Host ('Research active: '+(Display-Text (Get-OptionalProperty $State 'research_active')))
    Write-Host ('Activity: '+(Display-Text (Get-OptionalProperty $State 'activity_status')))
    Write-Host ('Stop requested: '+(Display-Text (Get-OptionalProperty $State 'stop_requested')))
    Write-Host ('Heartbeat age (seconds): '+(Display-Text (Get-OptionalProperty $State 'heartbeat_age_seconds')))
    Write-Host ('Controller PID: '+(Display-Text (Get-OptionalProperty $State 'controller_pid')))
    Write-Host 'Backends: Muse Wonder MAX through the budget guard; Claude Code subscription. No Claude API.'
    $reason=Get-OptionalProperty $State 'halt_reason'
    if ($null -ne $reason) { Write-Host ('Reason: '+(Display-Text $reason)) }
    $tasks=Get-OptionalProperty $State 'tasks'
    if ($null -ne $tasks) {
        Write-Host ''
        foreach($property in $tasks.PSObject.Properties) {
            $task=$property.Value
            Write-Host ('['+(Display-Text (Get-OptionalProperty $task 'phase'))+'] '+$property.Name+' | '+(Display-Text (Get-OptionalProperty $task 'provider')))
            $summary=Get-OptionalProperty $task 'summary'
            if ($null -ne $summary) { Write-Host ('  Model report (UNVERIFIED): '+(Display-Text $summary)) }
            $resultPath=Get-OptionalProperty $task 'result_path'
            if ($null -ne $resultPath) { Write-Host ('  Result: '+(Display-Text $resultPath 400)) }
            foreach($field in @('local_worker_exited','remote_unconfirmed','remote_uncertain')) {
                $value=Get-OptionalProperty $task $field
                if ($null -ne $value) { Write-Host ('  '+$field+': '+(Display-Text $value)) }
            }
            $receipt=Get-OptionalProperty $task 'provider_receipt'
            foreach($field in @('remote_status','cancellation_confirmed','error_category','usage_status','cost_usd')) {
                $value=Get-OptionalProperty $receipt $field
                if ($null -ne $value) { Write-Host ('  '+$field+': '+(Display-Text $value)) }
            }
        }
    }
    $budget=Get-OptionalProperty $State 'budget'
    if ($null -ne $budget) {
        $providers=Get-OptionalProperty $budget 'providers'
        if ($null -eq $providers) { $providers=$budget }
        foreach($name in @('meta','claude')) {
            $provider=Get-OptionalProperty $providers $name
            if ($null -ne $provider) {
                Write-Host ('Local '+$name+' ledger: committed $'+(Display-Text (Get-OptionalProperty $provider 'committed_usd'))+' / cap $'+(Display-Text (Get-OptionalProperty $provider 'cap_usd'))+'; available $'+(Display-Text (Get-OptionalProperty $provider 'available_usd')))
            }
        }
    } else { Write-Host 'Budget snapshot: not available in this status response.' }
    Write-Host 'Local ledger figures include holds; they are not verified provider balances.'
    Write-Host 'SUCCEEDED means a completed model response, not a verified proof. All research claims remain UNVERIFIED.'
}

function Request-AllStop {
    $receipt=Invoke-TeamController -ControllerArguments @('stop','--wait-seconds','85')
    Write-Host 'Stop receipt (all team runs):'
    Write-Output ($receipt | ConvertTo-Json -Depth 10)
    Write-Host 'A requested stop is not confirmation of remote cancellation; uncertain charges stay reserved.'
    try { Show-TeamStatus (Invoke-TeamController -ControllerArguments @('status')) }
    catch { Write-Warning 'Current-run status is unavailable. Preserve the stop receipt; do not clear STOP or retry a model request.' }
}

function Start-Team {
    foreach($marker in @((Join-Path $script:TeamRoot 'STOP'),(Join-Path $script:LabRoot 'continuation\STOP'))) {
        if (Test-Path -LiteralPath $marker) { throw 'A STOP marker is set. Start does not clear it; a reviewed reset is required.' }
    }
    $runtime=Get-ReviewedRuntime
    $arguments=@('create','--queue',$script:QueuePath,'--meta-backend','muse-wonder-api')
    if ($Simulate) { $arguments+=@('--simulate','--simulate-seconds',[string]$SimulateSeconds) }
    $created=Invoke-TeamController -ControllerArguments $arguments
    $runId=Get-OptionalProperty $created 'run_id'
    if (($runId -isnot [string]) -or $runId -cnotmatch '^[0-9a-f]{32}$') { throw 'Controller returned an invalid run ID; no child was launched.' }
    $runFolder=Join-Path $script:TeamRoot ('runs\'+$runId)
    if (-not (Test-Path -LiteralPath $runFolder -PathType Container)) { throw 'Created run folder was not found; no child was launched.' }
    $stdout=Join-Path $runFolder 'controller-stdout.log'
    $stderr=Join-Path $runFolder 'controller-stderr.log'
    $launchPath=Join-Path $runFolder 'launcher.json'
    foreach($path in @($stdout,$stderr,$launchPath)) {
        if (Test-Path -LiteralPath $path) { throw 'Launch artifacts already exist; refusing to overwrite or retry this run.' }
    }
    try {
        $savedEnvironment=@{}
        try {
            foreach($name in @('__PYVENV_LAUNCHER__','PYTHONHOME','PYTHONPATH')) {
                $savedEnvironment[$name]=[Environment]::GetEnvironmentVariable($name,'Process')
                [Environment]::SetEnvironmentVariable($name,$null,'Process')
            }
            $nativeArguments=@('-I','-S','-B','-X','utf8',('"'+$runtime.bootstrap+'"'),'run','--run-id',$runId)
            $process=Start-Process -FilePath $runtime.python_executable -ArgumentList $nativeArguments -WorkingDirectory $script:LabRoot -WindowStyle Hidden -RedirectStandardOutput $stdout -RedirectStandardError $stderr -PassThru
        } finally {
            foreach($name in $savedEnvironment.Keys) { [Environment]::SetEnvironmentVariable($name,$savedEnvironment[$name],'Process') }
        }
        $launch=@{run_id=$runId;controller_pid=$process.Id;launched_utc=[DateTimeOffset]::UtcNow.ToString('o');simulate=[bool]$Simulate;stdout=$stdout;stderr=$stderr}
        [IO.File]::WriteAllText($launchPath,($launch | ConvertTo-Json -Depth 4),[Text.UTF8Encoding]::new($false))
        Write-Host ('Created run '+$runId+'; controller PID '+$process.Id+'.')
        Write-Host ('Run folder: '+$runFolder)
        $clock=[Diagnostics.Stopwatch]::StartNew()
        while($clock.Elapsed.TotalSeconds -lt 30) {
            $process.Refresh()
            if ($process.HasExited) { throw 'Controller exited during startup. Inspect STATUS and the scoped stderr log; no automatic restart was made.' }
            try {
                $state=Get-Content -LiteralPath (Join-Path $runFolder 'state.json') -Raw -Encoding UTF8 | ConvertFrom-Json
                $phase=Get-OptionalProperty $state 'phase'
                $epoch=Get-OptionalProperty $state 'heartbeat_epoch'
                $pidValue=Get-OptionalProperty $state 'controller_pid'
                if (($phase -eq 'RUNNING') -and ($pidValue -eq $process.Id) -and ($null -ne $epoch)) {
                    $age=[DateTimeOffset]::UtcNow.ToUnixTimeSeconds()-[double]$epoch
                    if ((-not [double]::IsNaN($age)) -and (-not [double]::IsInfinity($age)) -and $age -ge -5 -and $age -le 15) {
                        Write-Host 'Fresh controller heartbeat confirmed. This confirms startup, not a model result.'
                        Show-TeamStatus (Invoke-TeamController -ControllerArguments @('status','--run-id',$runId))
                        return
                    }
                }
            } catch {
                # An atomic metadata replacement can be briefly unreadable on Windows.
            }
            Start-Sleep -Milliseconds 250
        }
        throw 'Startup heartbeat was not confirmed within 30 seconds.'
    } catch {
        # A spawn may succeed before later startup bookkeeping fails.
        $stopRecorded=$false
        try {
            $stopReceipt=Invoke-TeamController -ControllerArguments @('stop','--run-id',$runId,'--wait-seconds','0')
            $stopRecorded=$true
            Write-Output ($stopReceipt | ConvertTo-Json -Depth 6)
        } catch {
            Write-Warning ('Stop recording could not be confirmed for run '+$runId+'. Use STOP-RESEARCH.cmd; do not retry START.')
        }
        if ($stopRecorded) { throw ('Startup failed after the launch attempt. Stop was requested for run '+$runId+'; inspect STATUS and scoped logs. No automatic retry.') }
        throw ('Startup failed after the launch attempt; stop confirmation is unavailable for run '+$runId+'. Use STOP-RESEARCH.cmd immediately.')
    }

}

$pushed=$false
try {
    if (-not (Test-Path -LiteralPath $script:PythonPath -PathType Leaf)) { throw 'Project Python is missing. Setup must be repaired before starting research.' }
    if (-not (Test-Path -LiteralPath $script:QueuePath -PathType Leaf)) { throw 'The reviewed research queue is missing.' }
    if ($Simulate -and $Action -ne 'Start') { throw 'Simulate is available only with Action Start.' }
    Push-Location -LiteralPath $script:LabRoot
    $pushed=$true
    if ($Action -eq 'Validate') {
        Write-Output (@{validated=$true;python=$script:PythonPath;queue=$script:QueuePath;module=$script:Module;model_requests=0;processes_started=0} | ConvertTo-Json)
    } elseif ($Action -eq 'Start') { Start-Team }
    elseif ($Action -eq 'Status') { Show-TeamStatus (Invoke-TeamController -ControllerArguments @('status')) }
    else { Request-AllStop }
    exit 0
} catch {
    Write-Error (Display-Text $_.Exception.Message 700) -ErrorAction Continue
    exit 1
} finally {
    if ($pushed) { Pop-Location }
}
