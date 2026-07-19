[CmdletBinding()]
param(
    [ValidateRange(0, 1000)]
    [int]$Warmup = 0,

    [ValidateRange(1, 1000)]
    [int]$Repetitions = 1,

    [ValidateSet('Both', 'RustFirst', 'CppFirst')]
    [string]$Orders = 'Both',

    [string]$RunId = (Get-Date -Format 'yyyyMMdd-HHmmss'),

    [string]$Python = 'python',

    [string]$RustExe,

    [string]$CppExe,

    [switch]$Build,

    [switch]$ValidateOnly
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..'))
$datasetRoot = Join-Path $repoRoot 'datasets'
$generator = Join-Path $PSScriptRoot 'generate_manifest.py'
$outputRoot = Join-Path $repoRoot (Join-Path 'target\parity\full-corpus' $RunId)
$manifest = Join-Path $outputRoot 'manifest.tsv'

if (-not $RustExe) {
    $RustExe = Join-Path $repoRoot 'target\release\cobra-parity-rust.exe'
}
if (-not $CppExe) {
    $CppExe = Join-Path $repoRoot 'target\parity\cpp-ninja\cobra-parity-cpp.exe'
}
$RustExe = [IO.Path]::GetFullPath($RustExe)
$CppExe = [IO.Path]::GetFullPath($CppExe)

function Invoke-Checked {
    param(
        [Parameter(Mandatory)]
        [string]$FilePath,

        [Parameter(Mandatory)]
        [string[]]$Arguments,

        [Parameter(Mandatory)]
        [string]$Description
    )

    & $FilePath @Arguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Description failed with exit code $LASTEXITCODE"
    }
}

function Write-Metadata {
    $metadata.updated_at = (Get-Date).ToString('o')
    $metadata | ConvertTo-Json -Depth 12 |
        Set-Content -LiteralPath (Join-Path $outputRoot 'run.json') -Encoding utf8
}

function Get-JsonLineCount {
    param([string]$Path)

    if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
        return 0
    }
    $count = 0
    foreach ($null in [IO.File]::ReadLines($Path)) {
        $count++
    }
    return $count
}

function Export-EngineFailures {
    param(
        [Parameter(Mandatory)]
        [string]$InputPath,

        [Parameter(Mandatory)]
        [string]$OutputPath
    )

    if (-not (Test-Path -LiteralPath $InputPath -PathType Leaf)) {
        return 0
    }

    $failureCount = 0
    $writer = [IO.StreamWriter]::new($OutputPath, $false, [Text.UTF8Encoding]::new($false))
    try {
        foreach ($line in [IO.File]::ReadLines($InputPath)) {
            if ([string]::IsNullOrWhiteSpace($line)) {
                continue
            }
            try {
                $record = $line | ConvertFrom-Json
            }
            catch {
                $writer.WriteLine($line)
                $failureCount++
                continue
            }

            $signatureFailure =
                ($record.signature_len -ne $record.output_signature_len) -or
                ($record.signature_hash -ne $record.output_signature_hash)
            $probeFailure =
                ($record.full_width_probe_equivalent -ne $true) -or
                ($record.full_width_probe_mismatch_count -ne 0) -or
                ($record.input_full_width_hash -ne $record.output_full_width_hash)
            $runnerFailure =
                ($record.outcome -eq 'error') -or
                ($record.outcome -like '*_error') -or
                ($record.deterministic -ne $true)

            if ($signatureFailure -or $probeFailure -or $runnerFailure) {
                $writer.WriteLine($line)
                $failureCount++
            }
        }
    }
    finally {
        $writer.Dispose()
    }
    return $failureCount
}

function Invoke-Runner {
    param(
        [Parameter(Mandatory)]
        [string]$Label,

        [Parameter(Mandatory)]
        [ValidateSet('rust', 'cpp')]
        [string]$Engine,

        [Parameter(Mandatory)]
        [string]$Executable
    )

    $resultPath = Join-Path $outputRoot "$Label.jsonl"
    $stdoutPath = Join-Path $outputRoot "$Label.stdout.log"
    $stderrPath = Join-Path $outputRoot "$Label.stderr.log"
    $failurePath = Join-Path $outputRoot "$Label.failures.jsonl"
    $started = Get-Date
    $stopwatch = [Diagnostics.Stopwatch]::StartNew()

    Write-Host "[$Label] starting at $($started.ToString('o'))"
    & $Executable `
        --manifest $manifest `
        --output $resultPath `
        --warmup $Warmup `
        --repetitions $Repetitions `
        1> $stdoutPath 2> $stderrPath
    $exitCode = $LASTEXITCODE
    $stopwatch.Stop()

    $recordCount = Get-JsonLineCount -Path $resultPath
    $failureCount = Export-EngineFailures -InputPath $resultPath -OutputPath $failurePath
    $run = [ordered]@{
        label = $Label
        engine = $Engine
        executable = $Executable
        started_at = $started.ToString('o')
        finished_at = (Get-Date).ToString('o')
        elapsed_seconds = $stopwatch.Elapsed.TotalSeconds
        exit_code = $exitCode
        record_count = $recordCount
        engine_failure_count = $failureCount
        result = $resultPath
        failures = $failurePath
        stdout = $stdoutPath
        stderr = $stderrPath
    }
    $metadata.runs[$Label] = $run
    Write-Metadata

    Write-Host "[$Label] exit=$exitCode records=$recordCount failures=$failureCount elapsed=$($stopwatch.Elapsed)"
    return $run
}

function Invoke-Comparison {
    param(
        [Parameter(Mandatory)]
        [string]$OrderName,

        [Parameter(Mandatory)]
        [Collections.IDictionary]$RustRun,

        [Parameter(Mandatory)]
        [Collections.IDictionary]$CppRun
    )

    if ($RustRun.exit_code -ne 0 -or $CppRun.exit_code -ne 0) {
        $metadata.comparisons[$OrderName] = [ordered]@{
            skipped = $true
            reason = 'one or both runners returned a nonzero exit code'
        }
        Write-Metadata
        return
    }
    if ($RustRun.record_count -ne $metadata.manifest_case_count -or
        $CppRun.record_count -ne $metadata.manifest_case_count) {
        $metadata.comparisons[$OrderName] = [ordered]@{
            skipped = $true
            reason = 'one or both result files are incomplete'
        }
        Write-Metadata
        return
    }

    $summaryPath = Join-Path $outputRoot "$OrderName.comparison.json"
    $mismatchPath = Join-Path $outputRoot "$OrderName.mismatches.jsonl"
    $started = Get-Date
    $stopwatch = [Diagnostics.Stopwatch]::StartNew()
    $semanticFields = @(
        'expression',
        'bitwidth',
        'max_vars',
        'outcome',
        'signature_len',
        'signature_hash',
        'output_signature_len',
        'output_signature_hash',
        'full_width_probe_algorithm',
        'full_width_probe_count',
        'input_full_width_hash',
        'output_full_width_hash',
        'full_width_probe_equivalent',
        'full_width_probe_mismatch_count'
    )
    $stages = @('parse', 'signature', 'simplify', 'render')
    $ratioLogSums = @{}
    $ratioCounts = @{}
    foreach ($stage in $stages) {
        $ratioLogSums[$stage] = 0.0
        $ratioCounts[$stage] = 0
    }
    $strictMismatchCount = 0
    $mismatchCases = [Collections.Generic.HashSet[string]]::new()
    $commonCaseCount = 0

    $rustReader = [IO.StreamReader]::new($RustRun.result, [Text.Encoding]::UTF8)
    $cppReader = [IO.StreamReader]::new($CppRun.result, [Text.Encoding]::UTF8)
    $mismatchWriter = [IO.StreamWriter]::new(
        $mismatchPath,
        $false,
        [Text.UTF8Encoding]::new($false)
    )
    try {
        while (-not $rustReader.EndOfStream -and -not $cppReader.EndOfStream) {
            $rustLine = $rustReader.ReadLine()
            $cppLine = $cppReader.ReadLine()
            $rustRecord = $rustLine | ConvertFrom-Json
            $cppRecord = $cppLine | ConvertFrom-Json
            $commonCaseCount++
            $caseId = [string]$rustRecord.case_id

            $differences = [Collections.Generic.List[object]]::new()
            if ($rustRecord.case_id -ne $cppRecord.case_id) {
                $differences.Add([ordered]@{
                    case_id = $caseId
                    field = 'case_id'
                    rust = $rustRecord.case_id
                    cpp = $cppRecord.case_id
                })
            }
            if ($rustRecord.deterministic -ne $true) {
                $differences.Add([ordered]@{
                    case_id = $caseId
                    field = 'rust.deterministic'
                    rust = $rustRecord.deterministic
                })
            }
            if ($cppRecord.deterministic -ne $true) {
                $differences.Add([ordered]@{
                    case_id = $caseId
                    field = 'cpp.deterministic'
                    cpp = $cppRecord.deterministic
                })
            }

            foreach ($engineRecord in @(
                [ordered]@{ name = 'rust'; record = $rustRecord },
                [ordered]@{ name = 'cpp'; record = $cppRecord }
            )) {
                $record = $engineRecord.record
                if ($record.signature_len -ne $record.output_signature_len -or
                    $record.signature_hash -ne $record.output_signature_hash) {
                    $differences.Add([ordered]@{
                        case_id = $caseId
                        field = "$($engineRecord.name).boolean_signature_equivalent"
                        engine = $engineRecord.name
                    })
                }
                if ($record.full_width_probe_equivalent -ne $true -or
                    $record.full_width_probe_mismatch_count -ne 0 -or
                    $record.input_full_width_hash -ne $record.output_full_width_hash) {
                    $differences.Add([ordered]@{
                        case_id = $caseId
                        field = "$($engineRecord.name).full_width_probe_equivalent"
                        engine = $engineRecord.name
                        mismatch_count = $record.full_width_probe_mismatch_count
                    })
                }
            }

            foreach ($field in $semanticFields) {
                if ($rustRecord.$field -ne $cppRecord.$field) {
                    $differences.Add([ordered]@{
                        case_id = $caseId
                        field = $field
                        rust = $rustRecord.$field
                        cpp = $cppRecord.$field
                    })
                }
            }

            foreach ($difference in $differences) {
                $mismatchWriter.WriteLine(
                    ($difference | ConvertTo-Json -Compress -Depth 8)
                )
                $strictMismatchCount++
                [void]$mismatchCases.Add($caseId)
            }

            foreach ($stage in $stages) {
                $rustValues = @($rustRecord.timings_ns.$stage | Sort-Object)
                $cppValues = @($cppRecord.timings_ns.$stage | Sort-Object)
                $rustMiddle = [int][Math]::Floor($rustValues.Count / 2)
                $cppMiddle = [int][Math]::Floor($cppValues.Count / 2)
                if (($rustValues.Count % 2) -eq 0) {
                    $rustMedian = ($rustValues[$rustMiddle - 1] + $rustValues[$rustMiddle]) / 2.0
                }
                else {
                    $rustMedian = [double]$rustValues[$rustMiddle]
                }
                if (($cppValues.Count % 2) -eq 0) {
                    $cppMedian = ($cppValues[$cppMiddle - 1] + $cppValues[$cppMiddle]) / 2.0
                }
                else {
                    $cppMedian = [double]$cppValues[$cppMiddle]
                }
                if ($rustMedian -gt 0 -and $cppMedian -gt 0) {
                    $ratioLogSums[$stage] += [Math]::Log($rustMedian / $cppMedian)
                    $ratioCounts[$stage]++
                }
            }
        }
        if (-not $rustReader.EndOfStream -or -not $cppReader.EndOfStream) {
            $difference = [ordered]@{
                case_id = $null
                field = 'result_length'
                rust_records = $RustRun.record_count
                cpp_records = $CppRun.record_count
            }
            $mismatchWriter.WriteLine(($difference | ConvertTo-Json -Compress))
            $strictMismatchCount++
            [void]$mismatchCases.Add('<manifest>')
        }
    }
    finally {
        $rustReader.Dispose()
        $cppReader.Dispose()
        $mismatchWriter.Dispose()
    }

    $aggregates = [ordered]@{}
    foreach ($stage in $stages) {
        $ratio = $null
        if ($ratioCounts[$stage] -gt 0) {
            $ratio = [Math]::Exp($ratioLogSums[$stage] / $ratioCounts[$stage])
        }
        $aggregates[$stage] = [ordered]@{
            geomean_rust_over_cpp = $ratio
            case_count = $ratioCounts[$stage]
        }
    }
    $stopwatch.Stop()
    $exitCode = if ($strictMismatchCount -eq 0) { 0 } else { 1 }
    $summary = [ordered]@{
        schema = 'cobra-parity-v2'
        comparison_mode = 'semantic-streaming'
        common_case_count = $commonCaseCount
        strict_mismatch_count = $strictMismatchCount
        strict_mismatch_case_count = $mismatchCases.Count
        timing_aggregates = $aggregates
        mismatch_file = $mismatchPath
    }
    $summary | ConvertTo-Json -Depth 8 |
        Set-Content -LiteralPath $summaryPath -Encoding utf8

    $metadata.comparisons[$OrderName] = [ordered]@{
        started_at = $started.ToString('o')
        finished_at = (Get-Date).ToString('o')
        elapsed_seconds = $stopwatch.Elapsed.TotalSeconds
        exit_code = $exitCode
        strict_mismatch_count = $strictMismatchCount
        summary = $summaryPath
        mismatches = $mismatchPath
    }
    Write-Metadata
    Write-Host "[$OrderName comparison] cases=$commonCaseCount mismatches=$strictMismatchCount elapsed=$($stopwatch.Elapsed)"
}

if (-not (Test-Path -LiteralPath $datasetRoot -PathType Container)) {
    throw "Dataset directory not found: $datasetRoot"
}
if (-not (Test-Path -LiteralPath $generator -PathType Leaf)) {
    throw "Manifest generator not found: $generator"
}
$datasetFiles = @(
    Get-ChildItem -LiteralPath $datasetRoot -Recurse -File -Filter '*.txt' |
        Sort-Object FullName
)
if ($datasetFiles.Count -eq 0) {
    throw "No .txt datasets found below $datasetRoot"
}

if ($ValidateOnly) {
    Write-Host "Validation successful."
    Write-Host "Repository: $repoRoot"
    Write-Host "Datasets:   $($datasetFiles.Count)"
    Write-Host "Rust exe:   $RustExe"
    Write-Host "C++ exe:    $CppExe"
    Write-Host "No manifest was generated and no benchmark process was launched."
    return
}

if (Test-Path -LiteralPath $outputRoot) {
    throw "Run output already exists: $outputRoot. Choose a different -RunId."
}
New-Item -ItemType Directory -Path $outputRoot | Out-Null

if ($Build) {
    Push-Location $repoRoot
    try {
        Invoke-Checked -FilePath 'cargo' -Arguments @(
            'build', '--release', '--features', 'parity-tools', '--bin', 'cobra-parity-rust'
        ) -Description 'Rust parity runner build'
        Invoke-Checked -FilePath 'cmake' -Arguments @(
            '--build', (Join-Path $repoRoot 'target\parity\cpp-ninja'),
            '--target', 'cobra-parity-cpp'
        ) -Description 'C++ parity runner build'
    }
    finally {
        Pop-Location
    }
}

if (-not (Test-Path -LiteralPath $RustExe -PathType Leaf)) {
    throw "Rust runner not found: $RustExe. Build it first or pass -Build."
}
if (-not (Test-Path -LiteralPath $CppExe -PathType Leaf)) {
    throw "C++ runner not found: $CppExe. Build it first or pass -Build."
}

$metadata = [ordered]@{
    schema = 'cobra-full-corpus-run-v1'
    run_id = $RunId
    created_at = (Get-Date).ToString('o')
    updated_at = (Get-Date).ToString('o')
    repository = $repoRoot
    dataset_root = $datasetRoot
    datasets = @($datasetFiles.FullName)
    manifest = $manifest
    manifest_case_count = 0
    warmup = $Warmup
    repetitions = $Repetitions
    orders = $Orders
    machine = [ordered]@{
        computer_name = $env:COMPUTERNAME
        os = [Environment]::OSVersion.VersionString
        processor = $env:PROCESSOR_IDENTIFIER
        logical_processors = $env:NUMBER_OF_PROCESSORS
        power_plan = (& powercfg /getactivescheme 2>$null | Out-String).Trim()
    }
    revisions = [ordered]@{
        rust = (& git -C $repoRoot rev-parse HEAD 2>$null | Out-String).Trim()
        cpp = (& git -C 'D:\binsnake\CoBRA-cpp' rev-parse HEAD 2>$null | Out-String).Trim()
    }
    runs = [ordered]@{}
    comparisons = [ordered]@{}
}
Write-Metadata

$generatorArguments = @(
    $generator,
    '--suite', 'regression',
    '--no-builtins',
    '--dataset-limit', '0',
    '--output', $manifest
)
foreach ($dataset in $datasetFiles) {
    $generatorArguments += @('--dataset', $dataset.FullName)
}
Invoke-Checked -FilePath $Python -Arguments $generatorArguments -Description 'full-corpus manifest generation'

$manifestCaseCount = 0
foreach ($line in [IO.File]::ReadLines($manifest)) {
    if (-not [string]::IsNullOrWhiteSpace($line) -and -not $line.TrimStart().StartsWith('#')) {
        $manifestCaseCount++
    }
}
$metadata.manifest_case_count = $manifestCaseCount
Write-Metadata
Write-Host "Manifest contains $manifestCaseCount cases from $($datasetFiles.Count) dataset files."

if ($Orders -eq 'Both' -or $Orders -eq 'RustFirst') {
    $rustFirstRust = Invoke-Runner -Label 'rust-first.rust' -Engine rust -Executable $RustExe
    $rustFirstCpp = Invoke-Runner -Label 'rust-first.cpp' -Engine cpp -Executable $CppExe
    Invoke-Comparison -OrderName 'rust-first' -RustRun $rustFirstRust -CppRun $rustFirstCpp
}

if ($Orders -eq 'Both' -or $Orders -eq 'CppFirst') {
    $cppFirstCpp = Invoke-Runner -Label 'cpp-first.cpp' -Engine cpp -Executable $CppExe
    $cppFirstRust = Invoke-Runner -Label 'cpp-first.rust' -Engine rust -Executable $RustExe
    Invoke-Comparison -OrderName 'cpp-first' -RustRun $cppFirstRust -CppRun $cppFirstCpp
}

$metadata.finished_at = (Get-Date).ToString('o')
Write-Metadata
Write-Host "Full-corpus run complete: $outputRoot"
