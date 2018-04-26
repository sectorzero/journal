# 1. Notes for Rust

<!-- TOC -->

- [1. Notes for Rust](#1-notes-for-rust)
    - [1.1. Install](#11-install)
        - [1.1.1. Instructions](#111-instructions)
    - [1.2. Additional Tools](#12-additional-tools)
    - [1.3. IDE](#13-ide)
    - [1.4. Doc](#14-doc)
    - [1.5. References](#15-references)

<!-- /TOC -->

## 1.1. Install
- Install - rustup.rs
- Download and execute on the shell
- No sudo required
- Test
```text
/tmp » rustc --version
rustc 1.25.0 (84203cac6 2018-03-25)

/tmp » cargo --version
cargo 0.26.0 (41480f5cc 2018-02-26)

/tmp » rustup --version
rustup 1.11.0 (e751ff9f8 2018-02-13)
```
- [Source Install](https://gist.github.com/dearmark/90a7da8904111466b8b2c47d1678485b)

### 1.1.1. Instructions
- http://asquera.de/blog/2017-03-03/setting-up-a-rust-devenv/
- https://fungos.github.io/blog/2017/08/12/setting-up-a-rust-environment-on-windows/

## 1.2. Additional Tools

## 1.3. IDE

- Surpsingly IntelliJ is pathetic
    - linting does not work
    - debugging non-existent feature as it requires you to buy clion
    - pros : completion, go-to-defn/decl works great

- VSCode
    - Only known editor with debugging integration ( uses lldb on Mac OS X )
    - Also well-known configurations for Windows
    - Still trying out how the overall experience is
    - https://booyaa.wtf/2017/rust-vscode/index.html, https://www.ncameron.org/blog/what-the-rls-can-do/

- Might be better to use both : 
    - Intellij for coding
    - Intellij still cannot complete some 'trait' type functions, but atleast I can jump to source and figure out stuff
    - VSCode is UNUSABLE for navigating code
    - VSCode for debugging ( completion and navigation sucks )

- Best usage pattern observed
    - Use IntelliJ for Edit/Compile/Edit cycle
    - Intellij also works great for Run, Run Tests etc
    - Use rust-lldb for debugging the program ( need proficiency in lldb debugging ). Biggest hinderance is setting breakpoints as no-visual-context

Feature | IntelliJ | VSCode(RLS)
---------|----------|---------
 Navigation/GoToDefn/LocalFile | Y | Y
 Navigation/GoToDefn/Global | Y | N
 Navigation/GoToDefn/Macro | Y | N
 Navigation/GoToDefn/RustSrc | Y | N
 Editing/Linting | N | Y
 Editing/Completion | Y ( better ) | Y
 Editing/SyntaxHighlighting | Y ( better ) | Y
 Debugging | N | Y (just ok) (rust-lldb w extension) 

 ## Debugging

 - LLDB directly works best
 - https://bryce.fisher-fleig.org/blog/debugging-rust-programs-with-lldb/index.html
 - https://developer.apple.com/library/content/documentation/General/Conceptual/lldb-guide/chapters/Introduction.html

 ```
 ~/Workplace/example(master*) » rust-lldb ./target/debug/example
(lldb) command source -s 0 '/tmp/rust-lldb-commands.geS6Qh'
Executing commands in '/tmp/rust-lldb-commands.geS6Qh'.
(lldb) command script import "/Users/sectorzero/.rustup/toolchains/nightly-x86_64-apple-darwin/lib/rustlib/etc/lldb_rust_formatters.py"
(lldb) type summary add --no-value --python-function lldb_rust_formatters.print_val -x ".*" --category Rust
(lldb) type category enable Rust
(lldb) target create "./target/debug/example"
Current executable set to './target/debug/example' (x86_64).
(lldb) breakpoint set -f main.rs -l 3
Breakpoint 1: where = example`example::is_north::h994e303dd1147b98 + 14 at main.rs:6, address = 0x0000000100000a4e
(lldb) process launch
Process 21320 launched: './target/debug/example' (x86_64)
2
Process 21320 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x0000000100000a4e example`example::is_north::h994e303dd1147b98(dir=South) at main.rs:6
   3   	pub enum AnotherEnum { Blah, Hum, Hoo }
   4
   5   	pub fn is_north(dir: Direction) -> bool {
-> 6   	    match dir {
   7   	        Direction::North => true,
   8   	        _ => false,
   9   	    }
Target 0: (example) stopped.
(lldb) frame variable
(example::Direction) dir = South
(lldb) bt
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
  * frame #0: 0x0000000100000a4e example`example::is_north::h994e303dd1147b98(dir=South) at main.rs:6
    frame #1: 0x0000000100000b94 example`example::main::h6ecbc45e3efd18e2 at main.rs:24
    frame #2: 0x0000000100000da2 example`std::rt::lang_start::_$u7b$$u7b$closure$u7d$$u7d$::hfa6ac09075cc5782 at rt.rs:74
    frame #3: 0x00000001000018f8 example`std::panicking::try::do_call::h6a08405978dfb407 [inlined] std::rt::lang_start_internal::_$u7b$$u7b$closure$u7d$$u7d$::h378cad8d85f40371 at rt.rs:59 [opt]
    frame #4: 0x00000001000018ec example`std::panicking::try::do_call::h6a08405978dfb407 at panicking.rs:304 [opt]
    frame #5: 0x000000010001bbaf example`__rust_maybe_catch_panic at lib.rs:105 [opt]
    frame #6: 0x0000000100009cc8 example`std::rt::lang_start_internal::h97f230ad9d3fa4d2 [inlined] std::panicking::try::hc919a75abb28f36a at panicking.rs:283 [opt]
    frame #7: 0x0000000100009c95 example`std::rt::lang_start_internal::h97f230ad9d3fa4d2 [inlined] std::panic::catch_unwind::h03a15160a8b25ea4 at panic.rs:361 [opt]
    frame #8: 0x0000000100009c95 example`std::rt::lang_start_internal::h97f230ad9d3fa4d2 at rt.rs:58 [opt]
    frame #9: 0x0000000100000d82 example`std::rt::lang_start::hd117bd07de926a46(main=&0x100000aa0, argc=1, argv=&0x7fff5fbff8f8) at rt.rs:74
    frame #10: 0x0000000100000d25 example`main + 37
    frame #11: 0x00007fff97202235 libdyld.dylib`start + 1
    frame #12: 0x00007fff97202235 libdyld.dylib`start + 1
(lldb) th conti
Resuming thread 0x162321 in process 21320
Process 21320 resuming
false
false
Process 21320 exited with status = 0 (0x00000000)
 ```

## 1.4. Doc

## 1.5. References