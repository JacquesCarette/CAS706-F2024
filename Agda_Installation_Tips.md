# Agda Installation Tips

Translated by macrohard's generative AI Copilot.

#### Install ghcup

```sh
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

#### Install ghc

```sh
ghcup tui
# Install ghc-9.10.1 in the text UI
```

#### Install Agda

I use `cabal`, but `stack` also works.

```sh
cabal update
cabal install Agda-2.7.0
```

#### Install Emacs

  Installation methods are omitted

- MacOS: Aquamacs

- Linux: Emacs

- Windows:

  - Install WSL2 first then install Emacs under Linux

  - Try VS code on your own.

#### Configure Agda in Emacs

If `agda` is successfully installed, you can try `agda-mode locate` to see if it outputs the location of the `agda2.el` file.

This `setup` will only add some settings to the `.emacs` configuration file.

```bash
agda-mode setup
```

- If `agda-mode setup` fails

Directly create or open the `~/.emacs` configuration file with a text editor and copy the following `elisp` code into `.emacs`.

```elisp
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

;; auto-load agda-mode for .agda and .lagda.md
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))

```

Emacs will read `.emacs` at startup. The first `load-file` function loads `agda2.el`, which is the Emacs package for Agda, containing functions related to the Agda development environment.

The other `setq` function defines variables to automatically load `agda2-mode` when opening files with `.agda` or `.lagda.md` extensions.

```bash
agda-mode compile
```

Compile `agda-mode`. After installing Emacs packages, they can be compiled into `.elc` files for faster execution. Emacs also prefers using compiled `.elc` files.

- If you are using Linux and Emacs with Spacemacs configuration, there is an existing Agda layer configuration.

#### Install plfa

- Clone plfa

```bash
git clone https://github.com/JacquesCarette/plfa.github.io/ plfa

git checkout feature-v2.7
```

- Install the standard library

```bash
git submodule update --init
```

- Configure the library, assuming the installation path of `plfa` is `~/plfa/`; the configuration location on MacOS is slightly different.

Agda reads the configuration file in the `~/.agda` directory at runtime to determine which libraries to load.

```bash
mkdir -p ~/.agda

cp ~/plfa/data/dotagda/* ~/.agda
```

#### Configure Library for Assignment A1

Add the following lines to `~/.agda/defaults`

```script
CAS706
Exercises
```

Add the following lines to `~/.agda/libraries`

```script
$HOME/CAS706-F2024/Exercises.agda-lib
$HOME/CAS706-F2024/CAS706.agda-lib
```

Note that `~/.agda` is the directory where Agda configuration files are located, which might be different on MacOS.

Similarly, `$HOME/CAS706-F2024` is the location of the course repository, and it needs to be adjusted according to your personal setup.
