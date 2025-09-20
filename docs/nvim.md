# <span class="hl warn">NeoVim</span>
[TOC]
???+ success "reference"
    [1] [Bilibili Neovim初学者教程](https://www.bilibili.com/video/BV1N6ZRY7Etj/?spm_id_from=333.1391.0.0&p=5&vd_source=be3fd08fda4ebae5d312804342bfa60d)   
    [2] [NeoVim Release Page](https://github.com/neovim/neovim/releases/)
严格来讲，neovim（或vi/vim/gvim, Anyway）并非EDA工具，而是代码编辑和查看工具。   
由于对其的使用贯穿在IC设计验证过程之中，属于是时时刻刻都在见到（数字IC工程师的屏幕上：verdi波形+gvim的代码或log界面），因此值得学习和精进。

## install  
考虑到可移植性和可适配性，这里采用的是appimage解压的方式，实用性最广（因为appimage直接运行还需要系统有FUSE），这样b既可以在自己的personal PC上配置，也可以在Server的Linux系统中配置。 

首先需要保证glibc版本支持，运行  
```shell
ldd --version
```
<div class="hb warn">
<b>本机的glibc版本必须满足neovim安装要求</b>（例如NeoVim 0.11.4 要求glibc >= 2.12）<br>   
否则需要<b>用老版本的glibc来编译源码</b>或者<b>选择老版本的、支持本机glibc的Neovim</b>（显然后者的成功概率应当大一些）    
</div>
接着下载合适版本、指令集架构的appimage，接下并执行   
```bash
./nvim-linux-x86_64.appimage --appimage-extract
./squashfs-root/usr/bin/nvim
```
执行没有问题，那就可以为其添加alias，比如n，然后就可以用n键光速召唤nvim了   
## 基础配置（基于lua）
先建立如下配置文件结构，`~/.config/nvim/`这是nvim的default搜索路径, 默认吃`init.lua`和`lua文件夹`下的所有lua脚本，通过init.lua里面的`require("dir1.dir2.module")`联系起来，配置也向下兼容支持vim配置的vim scripts文件   
![alt text](img/image-26.png#img60)   
### 基本功能配置
![alt text](img/image-27.png#img60)  
```bash
vim.opt.number = true                                                   
vim.opt.relativenumber = true                                           
                                                                           
vim.opt.cursorline = true                                               
vim.opt.colorcolumn = "80"                                              
                                                                           
vim.opt.expandtab = true                                                
vim.opt.tabstop = 4                                                     
vim.opt.shiftwidth = 0                                                  
                                                                           
vim.opt.autoread = true
```
### 键盘映射配置

![alt text](img/image-28.png#img70)
```bash
vim.keymap.set({"n","i"},"<C-z>","<Cmd>undo<CR>",{silent = true})
vim.keymap.set({"n","i"},"<C-r>","<Cmd>redo<CR>",{silent = true})
```
## 准备安装Lazy插件
###安装nerd字体
在[nerdfonts官网](https://www.nerdfonts.com/font-downloads)下载JetBrainsMonoNerdFont字体       
下载后解压，将JetBrainsMonoNerdFontMono-Medium.ttf移动到`~/.local/share/fonts`下，并执行     
```shell
fc-cache -fv
```
刷新字体缓存，成功安装字体