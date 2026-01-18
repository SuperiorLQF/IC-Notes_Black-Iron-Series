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
如果你用verdi比较6，就会知道里面有个expand delta功能,可以分析组合逻辑竞争冒险等问题（前提是VCS得开glitch记录等功能）<br>   
或者你对SystemC的调度Region比较熟悉，你就会知道delta $\Delta$这个概念   
</div>
这里以SystemC为例，介绍一下SystemC中的仿真调度原理及$\Delta$  
 
SystemC中有**进程**的概念，进程只有被**触发**才会执行。有的进程(<b>SC_CTHREAD</b>)在时钟沿触发(时序逻辑)，有的进程(<b>SC_METHOD</b>)是根据敏感信号触发（组合逻辑）。

进程除了被触发，还可以被挂起。  

-  在时钟触发线程中，使用wait()来挂起，等待下次时钟触发。  
-  而组合逻辑的线程中，程序被执行完就自动挂起，等待下次敏感信号变化触发。  
   
进程的程序通过`a.write()`向信号写入值，该值并不会随着`write()`的调用立即写入，而是在进程挂起后，在后台**自动**等待$\Delta$时间完成更新(自动，即这是仿真内核自动完成的)       

很容易理解，从进程触发（或者叫被调度）到进程被挂起，是不需要消耗仿真时间的（连$\Delta$也不需要），所以评估（Evaluate，图上的E）发生在进程触发时刻，而更新（Update，图上的U）发生在进程挂起后$\Delta$

例子中信号A是时序信号，在时钟上升沿驱动。B是组合逻辑，敏感信号是A。  
A信号相关逻辑的进程在T0时刻被时钟上升沿触发，进入调度(<b>黄色的E</b>)，在评估中判断值为1，然后执行到wait()语句挂起。在$T_0+\Delta$时刻被自动更新为1.   
而B信号在$T_0+\Delta$被A信号的变化触发，进入调度(<b>粉色的E</b>)，评估值为`!1`，即0，执行完毕挂起，在$T_0+2\Delta$时刻被自动更新为0.

![alt text](img/image-36.png#img90)   
对应的波形示意图如下   
![alt text](img/image-37.png#img50)   

## 三、TODO

## 四、抽象接口:sc_port和sc_interface
用户自定义接口类是一个**虚基类**，需要继承自sc_interface,并在里面声明虚函数(抽象函数，声明各种行为)，定义通道需要的服务，但不实现。
```C++
class mst_if : public sc_interface {
public:
    virtual void send(int data) = 0; // 发送数据
    virtual bool is_ready() = 0;     // 查询从设备是否就绪
};
```

实现接口是在module里面实现的，module除了继承自sc_module外，还需要继承刚才实现的用户接口类,并overrride的方式实现接口中的虚函数
```C++
SC_MODULE(Master) {
    sc_port<mst_if> mst_port;  // 通过端口访问接口
    void process() {
        if (mst_port->is_ready()) {      // 调用接口方法
            mst_port->send(42);
        }
    }
    SC_CTOR(Master) { SC_THREAD(process); }
};
```
通道,是接口的具体实现，继承自接口，用于在模块间传输数据，也管理底层信号逻辑
```C++
class my_channel : public sc_channel, public my_interface {
private:
    int data;
public:
    void write(int val) override { data = val; }
    int read() override { return data; }
};
```
端口sc_port<InterfaceType>是一个模板类，模板可以填任何sc_interface的派生类，端口是模块访问接口的入口
端口分为port和export两种，其中export是模块将自身实现暴露给外部
端口，和常用的sc_in,sc_out这些普通port类似，sc_port也是模块与外部通信的媒介。**将接口调用方法转发到对应通道。**
sc_port通过->调用通道方法。

端口的连接，在顶层连接
```C++
my_channel channel("bus");  // 通道实例
Master mst("mst");
Slave slv("slv");
mst.port(channel);  // 端口绑定到通道
slv.port(channel);
```
简单概括就是，通过sc_port调用方法，如send；在通道里实现方法。