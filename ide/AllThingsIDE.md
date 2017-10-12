# All Things IDE

## Usability Requirements

- Vim as editing interface
- Go To
  1. Source
  1. Declaration / Definition
  1. Function / Method
  1. Class / Member
  1. File
- Unit Tests
- Run
- Debug
- Syntax & Common Error Linting
- Imports
- Completion Suggestions
- Snippets
- Solarized Color Theme
- Customizable Key Map

## Vim is an interface

## Platforms

- Mac OS X
- Windows

## Required IDEs

1. IntelliJ ( + Gogland )
1. Visual Studio 2017
1. Visual Studio Code

## Language Ecosystems

Language | Platform | IDE | Vim
---------|----------|-----|----
C/C++ | Windows | VisualStudio2017 | VsVim
Java | MacOSX | IntelliJ | IdeaVim
Go | MacOSX | Gogland | IdeaVim
Erlang | MacOSX | IntelliJ | IdeaVim
Markdown | MacOSX | VisualStudioCode | VsCodeVim

## Disk Benchmark

- Benchmarking Tool : _diskspd_
  ```text
     Random : diskspd.exe -b8K -d60 -h -L -o2 -t4 -r -w30 -c50M <drive>:\io.dat
     Seq :    diskspd.exe -c100G -d10 -w0 -t2 -o8 -b512K -h -L -si <drive>:ioseq.dat
  ```
- Platform :
  ```text
  OS Name   Microsoft Windows 10 Enterprise
  Version   10.0.15063 Build 15063
  OS Manufacturer   Microsoft Corporation
  System Manufacturer   HP
  System Model  HP Z240 Tower Workstation
  System Type   x64-based PC
  System SKU    L8T12AV
  Processor Intel(R) Core(TM) i7-6700 CPU @ 3.40GHz, 3401 Mhz, 4 Core(s), 8 Logical Processor(s)
  BIOS Version/Date HP N51 Ver. 01.58, 6/2/2017
  SMBIOS Version    2.7
  Embedded Controller Version   5.55
  BIOS Mode UEFI
  BaseBoard Manufacturer    HP
  BaseBoard Model   Not Available
  BaseBoard Name    Base Board
  Platform Role Workstation
  Secure Boot State On
  PCR7 Configuration    Elevation Required to View
  Hardware Abstraction Layer    Version = "10.0.15063.502"
  Installed Physical Memory (RAM)   64.0 GB
  Total Physical Memory 63.9 GB
  Available Physical Memory 56.2 GB
  Total Virtual Memory  73.4 GB
  Available Virtual Memory  65.1 GB
  Page File Space   9.50 GB
  ```

Name | Type | IOPS-8K-w30/r70 | Latency-p99-8K-w30/r70 | MBPS-Seq
-----|------|-----------------|------------------------|-------
[WD-Blue-1TB-2012](http://hdd.userbenchmark.com/WD-Blue-1TB-2012/Rating/1779) | Spinning | 510 | 21/108 | 165
[Samsung Client SSD](http://www.samsung.com/semiconductor/products/flash-storage/client-ssd/MZVKW512HMJP?ia=831) | SSD | 7398 | 4.8/7.5 | 3302
[Samsung EVO M.2 NVMe SSD](https://www.samsung.com/us/computing/memory-storage/solid-state-drives/ssd-960-evo-m-2-1tb-mz-v6e1t0bw/) | SSD | 48783 | 0.06/2.34 | 927
