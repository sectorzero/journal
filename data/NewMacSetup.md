
[TOC]

# Basic Preparation
* [Security](https://github.com/drduh/macOS-Security-and-Privacy-Guide)
* Bootup Diagnostics Check
  1. Power button to bootup
  1. Hold 'D'
  1. System should guide you through H/W diagnostics
  1. Ensure everything is OK
  1. Use the serial number and check if the h/w is registered/recognized with Apple
* Cold boot test
  1. Do a cold boot 2-3 times and ensure everything is ok
* First Boot 
  1. Do not connect to any network
  1. When prompted do not setup any wifi or any network access
  1. When prompted do not setup AppleId etc.
  1. Choose a temporary password for the account, which will become admin by default. We will change that later. 
* Setup after first boot to login with default admin account
  1. Keep network off
  1. Create a new admin account with strong password
  1. Log out of default admin account and log into admin account
  1. Drop privileges of default admin account to non-admin ( of preferably just ensure that the default admin account has strong password )
  1. Admin Account Settings
      1. Disable location tracking
      1. Ensure all other accounts have required privileges. Regular use account should not be admin
      1. Spotlight, remove most of the search spaces. Esp 'Spotlight Preferences'
      1. Keep Sharing Off for now
      1. Enable Firewall Full
      1. Login : always require password, as soon as locked, advanced : auto log off in 30 mins, always ask for admin password for systemwide changes
      1. Keychain Access : need to research 
  1. Create an account with fully restricted Guest user, in-case anybody wants to use your computer
  1. Reboot
  1. FileVault
      1. Turn off network
      1. Login as Admin
      1. Enable FileVault and enable full disk encryption
  1. Reboot
  1. Create network connection configurations and connect
  1. Install all required Security & Software Updates which are pending ( might have to run through few cycles of reboot )
  1. Reboot
  1. Always login to regular use account ( do not use admin account )
  1. Ensure everything works correctly

# Security
* [Security](https://github.com/drduh/macOS-Security-and-Privacy-Guide)

# Core Tooling Support
These are the only two basic core tooling support you will need to setup most of the software and applications. So setting these up correctly is critical to having an auditable, manageable and pain-free system later on.

## Git
1. Use Git via installing 'XCode CommandLine Tools'
    1. Install XCode from AppStore or developer.apple.com OR
    1. ```xcode-select --install``` in the terminal
2. Verify
```
$> git --version
git version 2.10.1 (Apple Git-78)
```
## Homebrew
* Default Homebrew setup tries to force you to always work logged in as an admin user. DO NOT DO THIS. I researched and found two ways and ultimately I settled for the more elegant and simple of the two approaches. The preferred approach has been documented below.
1. Follow this for setting up the basic Homebrew setup. [Setup](http://blog.strug.de/2012/06/my-homebrew-multi-user-setup/) 
2. With this you can install any software and tools managed by Homebrew repositories
3. For other 'Applications' managed by 'Cask' use the following to install any app : 
    1. Create an Applications directory under your home directory ( if not already exists ). Because Cask always tries to install into the System's Application directory you will not be able do so logged in as non-admin.
    1. To instally any ```<application>```, use the following full command-line. Just add it as a function in your .zshrc for convenience. 
    1. Note that you may need to exclude the ```--require-sha``` and ```--no-binaries``` for some special exclusions, but try to keep these on by default
      ```
      /usr/local/bin/brew cask install --verbose --require-sha --no-binaries --appdir=~/Applications <appname> 
      ```

# Directory / Files Organization
```
~/
  Applications/
  Desktop/
  Downloads/
  Documents/
  Data/
  Library/
  Workspace/
  Movies/
  Music/
  Pictures/
  Tools/
  Public/
```

# Shell Setup

# Github

# Chrome

# Basic Editors
## Vim
## Emacs ( via Spacemacs )

# Language / Development Enviroment Setup

## C/C++
## Rust
## Java
## Python
