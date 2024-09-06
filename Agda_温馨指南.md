# Agda温馨指南

#### 安装ghcup

```sh
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

#### 安装ghc

```sh
ghcup tui
# 在文字ui中安装 ghc-9.10.1
```

#### 安装agda

我用的是`cabal`，也可以用`stack`。

``` sh
cabal update
cabal install Agda-2.7.0
```

#### 安装Emacs

  安装方法略

- MacOS: Aquamacs

- Linux: Emacs

- Windows:

  - Install WSL2 first then install Emacs under Linux

  - Try VS code on purely yourself.

#### Emacs配置 agda

如果`agda`已经成功安装，可以尝试`agda-mode locate`来看是不是输出`agda2.el`文件的位置。

这个`setup`只会添加一些设置到`.emacs`配置文件。


```bash
agda-mode setup
```

- 如果`agda-mode setup`失败

直接用文本编辑器新建、打开`~/.emacs`配置文件，将以下`elisp`代码复制到`.emacs`里。

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

Emacs会在启动时读取`.emacs`。第一个`load-file`函数可以加载`agda2.el`，这是Emacs的agda包，包含agda开发环境相关的函数。

另一个`setq`函数定义变量，在加载`.agda`、`.lagda.md`后缀的文件时自动加载`agda2-mode`。

```bash
agda-mode compile
```

编译`agda-mode`。Emacs的包安装完毕之后可以编译成`.elc`，这样运行更快。而且Emacs也更偏好使用编译好的`.elc`。

- 如果是Linux，并且Emacs使用Spacemacs配置，有现存的agda layer配置。

#### 安装plfa

- 克隆plfa

```bash
git clone https://github.com/JacquesCarette/plfa.github.io/ plfa

git checkout feature-v2.7
```

- 安装标准库

```bash
git submodule update --init
```

- 配置库，假设 `plfa` 的安装路径是 `~/plfa/`；MacOS的配置位置有点不同

Agda在运行时会读取`~/.agda`目录下的配置文件，来确定加载的库。

```bash
mkdir -p ~/.agda

cp ~/plfa/data/dotagda/* ~/.agda
```

#### 配置作业A1的库

添加以下字符到`~/.agda/defaults`

```script
CAS706
Exercises
```

添加以下字符到`~/.agda/libraries`

```script
$HOME/CAS706-F2024/Exercises.agda-lib
$HOME/CAS706-F2024/CAS706.agda-lib
```

注意`~/.agda`是agda配置文件所在的目录，MacOS可能不同。

同理，`$HOME/CAS706-F2024`是课程repo的位置，需要根据个人设置来调整。
