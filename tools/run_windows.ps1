param(
    [ValidateSet('environment', 'core', 'build', 'module', 'lean', 'python',
        'metadata', 'compile', 'coverage', 'fresh', 'tests', 'processes', 'lookup')]
    [string]$Mode = 'environment',
    [string]$Target = ''
)

# Invoke the existing native toolchain from WSL without changing installations.
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $projectRoot
$env:Path = (Join-Path $env:USERPROFILE '.elan\bin') + ';' +
    (Join-Path $env:USERPROFILE 'AppData\Local\Programs\Python\Python313') + ';' +
    [Environment]::GetEnvironmentVariable('Path', 'Machine') + ';' +
    [Environment]::GetEnvironmentVariable('Path', 'User')
$OutputEncoding = [Console]::OutputEncoding = [Text.UTF8Encoding]::new($false)
$env:PATHEXT = '.COM;.EXE;.BAT;.CMD'
$env:PYTHONUTF8 = '1'
$env:PYTHONIOENCODING = 'utf-8'
$lakeCommand = Join-Path $env:USERPROFILE '.elan\bin\lake.exe'

function Invoke-Native([string]$Executable, [string[]]$Arguments) {
    $commandLine = '$ ' + $Executable + ' ' + ($Arguments -join ' ')
    Write-Output $commandLine
    $logDirectory = Join-Path $projectRoot 'verification\current'
    [IO.Directory]::CreateDirectory($logDirectory) | Out-Null
    # Concurrent checks must never overwrite or append to one another's evidence.
    $logName = 'native-' + $Mode + '-' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff') +
        '-' + [Guid]::NewGuid().ToString('N') + '.log'
    $logPath = Join-Path $logDirectory $logName
    $latestLogPath = Join-Path $logDirectory ('native-' + $Mode + '.log')
    Write-Output ('Log: ' + $logName)
    [IO.File]::WriteAllText($logPath, $commandLine + [Environment]::NewLine, [Text.UTF8Encoding]::new($false))
    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $Executable
    $startInfo.Arguments = $Arguments -join ' '
    $startInfo.WorkingDirectory = $projectRoot
    $startInfo.UseShellExecute = $false
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.StandardOutputEncoding = [Text.UTF8Encoding]::new($false)
    $startInfo.StandardErrorEncoding = [Text.UTF8Encoding]::new($false)
    $process = [Diagnostics.Process]::Start($startInfo)
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $process.WaitForExit()
    $stdoutText = $stdoutTask.GetAwaiter().GetResult()
    $stderrText = $stderrTask.GetAwaiter().GetResult()
    [IO.File]::AppendAllText($logPath, $stdoutText + $stderrText, [Text.UTF8Encoding]::new($false))
    if ($stdoutText) { Write-Output $stdoutText }
    if ($stderrText) { Write-Output $stderrText }
    $script:toolExitCode = $process.ExitCode
    [IO.File]::AppendAllText($logPath, ('Exit code: ' + $script:toolExitCode + [Environment]::NewLine), [Text.UTF8Encoding]::new($false))
    [IO.File]::Copy($logPath, $latestLogPath, $true)
    Write-Output ('Exit code: ' + $script:toolExitCode)
}

switch ($Mode) {
    'processes' {
        Get-Process | Where-Object { $_.ProcessName -in @('lean', 'lake', 'python', 'elan') } |
            Select-Object Id, ProcessName, CPU, StartTime, WorkingSet64, Path | Format-Table -AutoSize
        Get-CimInstance Win32_OperatingSystem |
            Select-Object TotalVisibleMemorySize, FreePhysicalMemory | Format-List
        Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'lean.exe' } |
            Select-Object ProcessId, CommandLine | Format-List
        $script:toolExitCode = 0
    }
    'environment' {
        Write-Output ('Working directory: ' + (Get-Location).Path)
        Write-Output ('USERPROFILE: ' + $env:USERPROFILE)
        Invoke-Native -Executable $lakeCommand -Arguments @('env', 'lean', '--version')
        Invoke-Native -Executable $lakeCommand -Arguments @('--version')
        $pythonCommand = (Get-Command python.exe -ErrorAction Stop).Source
        Invoke-Native -Executable $pythonCommand -Arguments @('--version')
    }
    'core' { Invoke-Native -Executable $lakeCommand -Arguments @('build', 'MonotoneOperators') }
    'build' { Invoke-Native -Executable $lakeCommand -Arguments @('build', 'MonotoneOperators', 'EndOfPaper', 'Paper') }
    'module' { Invoke-Native -Executable $lakeCommand -Arguments @('build', $Target) }
    'lean' { Invoke-Native -Executable $lakeCommand -Arguments @('env', 'lean', $Target) }
    'python' {
        $pythonCommand = (Get-Command python.exe -ErrorAction Stop).Source
        Invoke-Native -Executable $pythonCommand -Arguments @($Target)
    }
    'lookup' {
        $pythonCommand = (Get-Command python.exe -ErrorAction Stop).Source
        Invoke-Native -Executable $pythonCommand -Arguments @('tools/lookup.py', $Target)
    }
    { $_ -in 'metadata', 'compile', 'coverage', 'fresh', 'tests' } {
        $pythonCommand = (Get-Command python.exe -ErrorAction Stop).Source
        if ($Mode -eq 'tests') {
            $pythonArguments = @('-m', 'unittest', 'discover', '-s', 'tests', '-v')
        } elseif ($Mode -eq 'fresh') {
            $pythonArguments = @('tools/verify.py', '--compile', '--fresh')
        } else {
            $pythonArguments = @('tools/verify.py', ('--' + $Mode))
        }
        Invoke-Native -Executable $pythonCommand -Arguments $pythonArguments
    }
}
exit $script:toolExitCode
