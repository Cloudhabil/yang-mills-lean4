# PowerShell script to deploy yang-mills-lean4 wiki to GitHub Wiki tab
param(
    [string]$WikiRemote = "https://github.com/Cloudhabil/yang-mills-lean4.wiki.git"
)

$ErrorActionPreference = "Stop"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RepoRoot = Split-Path -Parent $ScriptDir
$WikiSrc = Join-Path $RepoRoot "wiki"
$TempWikiDir = Join-Path $RepoRoot ".temp_wiki_deploy"

Write-Host "=== Deploying yang-mills-lean4 Wiki Knowledge Base ===" -ForegroundColor Cyan
Write-Host "Source directory: $WikiSrc"
Write-Host "Remote wiki URL: $WikiRemote"

if (Test-Path $TempWikiDir) {
    Remove-Item -Recurse -Force $TempWikiDir
}

try {
    Write-Host "Cloning GitHub wiki repository..." -ForegroundColor Yellow
    git clone $WikiRemote $TempWikiDir
} catch {
    Write-Host "NOTE: If the wiki clone fails with 'Repository not found', please visit:" -ForegroundColor Red
    Write-Host "  https://github.com/Cloudhabil/yang-mills-lean4/wiki" -ForegroundColor Red
    Write-Host "and click the green 'Create the first page' button to initialize the wiki on GitHub." -ForegroundColor Red
    exit 1
}

Write-Host "Copying all 15 wiki files..." -ForegroundColor Yellow
Copy-Item -Path "$WikiSrc\*" -Destination $TempWikiDir -Recurse -Force

Push-Location $TempWikiDir
try {
    git add .
    git commit -m "docs(wiki): update 15-page complete Yang-Mills technical knowledge base"
    Write-Host "Pushing to GitHub Wiki..." -ForegroundColor Green
    git push origin master
    Write-Host "SUCCESS! Wiki is live at: https://github.com/Cloudhabil/yang-mills-lean4/wiki" -ForegroundColor Green
} finally {
    Pop-Location
    Remove-Item -Recurse -Force $TempWikiDir
}
