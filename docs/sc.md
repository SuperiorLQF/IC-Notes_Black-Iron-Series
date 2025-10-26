# <span class="hl">SystemC</span>
[TOC]
???+ success "<font size=3>reference</font>" 
    [1]  [https://www.learnsystemc.com/](https://www.learnsystemc.com/)   
    [2] 《SystemC Prime(夏宇闻 译)》  
    [3] 《SystemC 电子系统级设计》   
    [4]  [Bilibili SC视频短课](https://www.bilibili.com/video/BV1P54y1z77U/?spm_id_from=333.337.search-card.all.click&vd_source=be3fd08fda4ebae5d312804342bfa60d)  

## 一、环境搭建 
系统：Linux（Ubuntu 22.04）  
[SystemC库官网下载地址](https://www.accellera.org/downloads/standards/systemc)  
SystemC库版本：3.0.1  

### 1.下载官方库并解压

```bash
tar -zxvf systemc-3.0.1.tar.gz
```
### 2.配置CMake选项并安装
新的SystemC版本是基于CMake构建的，但是doc里缺少一些文件，所以先去CMakeLists里注释掉doc的编译，只编译核心库即可   
![alt text](img/image-33.png#img70)  

新建编译文件夹，在systemc-3.0.1的根目录下
```bash
mkdir build && cd build
```
接着抽取外部的CMkeLists, <span class="btlor">用命令行参数进行配置，选择合适的安装路径</span>（即吐出编译完的SystemC的库的位置）
```bash
cmake .. -DCMAKE_INSTALL_PREFIX=/path/to/install # 替换 /path/to/install 为安装路径
```
随后进行编译、安装
```bash
make clean
sudo make -j10
make install
```
到前面命令行参数给出的路径位置，输出了可以直接在工程中掉用的SystemC静态链接库文件夹（因为它是可移植的，所以叫安装也比较容易产生误导）

### 3.在工程中调用
我的SystemC仿真工程也采用`CMake`构建，文件层次如下图   
其中libs下的`systemc-3.0.1即`前面安装后生成的静态链接库，`cp`过来  
![alt text](img/image-34.png#img40)  
在`build`文件夹内进行构建工程，使用如下命令
```bash
cmake .. #读取CMakeLists
make #编译并运行仿真，dump波形
```
运行结果如下  
![alt text](img/image-35.png#img70)  


CMakeLists内容如下，可供参考(AI生成的)
```CMake
cmake_minimum_required(VERSION 3.10)
project(NocSim LANGUAGES CXX)

# 设定 C++ 标准（SystemC 3.0.1 需要至少 C++17）
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 源文件所在路径
set(SRC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../src")

# 自动收集所有 .cpp 源文件
file(GLOB_RECURSE SRC_FILES "${SRC_DIR}/*.cpp")

# SystemC 安装路径
set(SYSTEMC_DIR "${CMAKE_CURRENT_SOURCE_DIR}/libs/systemc-3.0.1")

# 头文件和库路径
include_directories("${SRC_DIR}")
include_directories("${SYSTEMC_DIR}/include")

link_directories("${SYSTEMC_DIR}/lib")

# 生成可执行文件
add_executable(test ${SRC_FILES})

# 链接 SystemC
target_link_libraries(test systemc m)

# 编译完成后自动执行可执行文件
add_custom_command(TARGET test
    POST_BUILD
    COMMAND ${CMAKE_CURRENT_BINARY_DIR}/test
    COMMENT "✅ 编译完成，正在自动运行 test..."
)
```
## 二、仿真调度原理delta
<div class =hb>
如果你用`verdi`比较6，就会知道里面有个expand delta功能,可以分析组合逻辑竞争冒险等问题（前提是VCS得开glitch记录等功能）<br>   
或者你对SystemC的调度Region比较熟悉，你就会知道delta $\Delta$这个概念   
</div>
这里以SystemC为例，介绍一下SystemC中的仿真调度原理及$\Delta$
