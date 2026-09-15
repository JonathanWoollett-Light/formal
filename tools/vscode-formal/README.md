# formal for Visual Studio Code

Syntax highlighting for the high-level dialect, the `.hl` files under
`tests/` and `std/`.

This is a TextMate grammar, not a language server. Highlighting in VS Code is
declarative: the editor colours a file from a set of regular expressions
(`syntaxes/formal.tmLanguage.json`) without running anything. A language
server is the mechanism for diagnostics, completion and go-to-definition, and
would be a process the editor talks to; nothing here needs one. The grammar
mirrors the Prism `formal` definition the website uses in
[index.html](../../index.html), so the two should be kept in step when the
language grows a keyword.

## Install

There is no build step and nothing to download. VS Code loads any folder in
its extensions directory that has a `package.json`, so copy or link this one:

```powershell
# Windows (PowerShell, from the repository root)
New-Item -ItemType SymbolicLink -Path "$env:USERPROFILE\.vscode\extensions\formal.vscode-formal-0.1.0" -Target "$PWD\tools\vscode-formal"
```

```sh
# macOS / Linux (from the repository root)
ln -s "$PWD/tools/vscode-formal" ~/.vscode/extensions/formal.vscode-formal-0.1.0
```

Then reload the window (`Developer: Reload Window`). `.hl` files pick up the
`formal` language automatically; the language mode indicator in the status
bar shows it, and `#` toggles a line comment.

A symbolic link means edits to the grammar here take effect on the next
reload, which is the right setup while the language is still moving. A copy
works the same but has to be refreshed by hand.

## What is coloured

| Text                                  | Scope                              |
| ------------------------------------- | ---------------------------------- |
| `# ...`                               | comment                            |
| `"..."`                               | string, with `\n`-style escapes    |
| `def name(`                           | keyword, then the function's name  |
| `name: ...` at the start of a line    | a variable definition              |
| `if` `while` `return` `require` `asm` | control keywords                   |
| `global` `thread`                     | locality                           |
| `u8` ... `i64`, `_`, `..`             | types and their placeholders       |
| `t0`-`t5`, `a0`-`a7`                  | registers                          |
| numbers, `0x...`, `0b...`             | numeric constants                  |
| `type(` `csr(`                        | builtins                           |
| `name(`                               | a call                             |
| `&name`, `+ - * / %`, `== != < > <= >=` | operators                        |

Lines inside an `asm:` block get the same treatment; the registers and
numbers in them are coloured, the mnemonics are left plain.
