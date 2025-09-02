# <span class="hl info">LFSR</span>(Linear Feedback Shift Register)
???+success "Reference"    
    [1]《Verilog高级数字系统设计与实例分析》  
    [2] [YouTube:computerphile LFSR](https://www.youtube.com/watch?v=Ks1pw1X22y4)   
    [3] [Tutorial: Linear Feedback Shift Registers (LFSRs)](https://www.edn.com/tutorial-linear-feedback-shift-registers-lfsrs-part-1/)   
    [4] [MicroZed Chronicles: Linear Feedback Shift Register](https://www.adiuvoengineering.com/post/microzed-chronicles-linear-feedback-shift-register)   
    [5] [CSDN:线性反馈移位寄存器(Linear Feedback Shift Register, LFSR)](https://blog.csdn.net/helaisun/article/details/103835889)

## 引入：衔尾之蛇
LSFR全称：<span class="btl">线性反馈移位寄存器</span>，由移位寄存器和异或门逻辑组成，下图是LSFR的一个例子
![alt text](img/image-17.png#img50)  
有Circuit和Symbol两种表示，通常用更简单的Symbol表示  
由于移位寄存器的输出被**反馈**了回去，可以形象地与<span class="hl">衔尾蛇Ouroboros</span>联系起来    

![alt text](img/image-16.png#img30)  
如下图所示，给定一个初始值，LSFR就会按照一定周期循环计数

![alt text](img/image-18.png#img30)  
<div class = "hb tip">

<font size=5>👉</font>由N个寄存器构成的LSFR，可能达到的最大周期是<font color =red>$2^N-1$</font>（只有特定的反馈结构才能达到最大计数周期，不同的<b>抽头(TAP)</b>位置会影响计数周期）</br>
<font size=5>👉</font>全0状态无法达到，初始值也禁止给全0，因为任意个0互相异或结果仍未0，会导致LFSR锁死     
</div> 
下图给出了不同比特下达到最大计数周期的抽头结构(<b><font color=purple>both适用于下一节中提到的两种结构</b></font>)   
<div class ="hb warn">
在固定比特数下，最大周期的结构可能不止一个，表上只写出一种。实际使用考虑逻辑门消耗，以TAP数少的为优
</div>
![alt text](img/image-22.png#img40)  
*Taps [a,b..]表示从寄存器a、b...输出引出抽头  
 
当然，非常容易得到，仅由XNOR组成的LFSR和XOR组成的LFSR是完全对偶的，包括XNOR LSFR状态不会出现全1
## 基本结构
LFSR分为两种结构：<span class="btl">斐波那契（Many-to-one）</span>和<span class="btl">伽罗瓦（One-to-Many）</span>，根据其英文名可以很容易分辨出结构的不同    
![alt text](img/image-20.png#img50)  
回顾一下异或操作有如下两个特性：  
![alt text](img/image-19.png#img30)  
因此，上图中的Many-to-one就可以看成1，2，3，7输出全部异或(⊕)在一起再给到0   
所以有了下图更为简洁的表示方法   

![alt text](img/image-21.png#img60)  
<div class = "hb tip">
<font size=5>👉</font>由于对偶性，Many-to-one和One-to-many在抽头结构相同情况下，计数周期也是相同的  <br>
<font size=5>❗</font>但是Many-to-one的多个异或门之间是级联而没有被寄存器打断，因此One-to-many的时序更好、频率可以做到更高  
</div>

## 应用
- LFSR计数器：相比传统计数器，LFSR<span class="btl">速度快，消耗逻辑门更少</span>  
- 产生伪随机序列：初始值称为seed   
- 扰码与解扰器（扰码使重复数据与图案频谱被展宽，数据被随机化，降低电磁干扰）  
- 密码系统  

???+ question "并行扰码器"
    <font size=3>对于需要LFSR输出8bit进行扰码的情况（如PCIe），可以假想一个虚拟时钟让寄存器链右移了8次    

    ![alt text](img/image-24.png#img80)  
    
    只要提前算出右移8bit后每个寄存器的值是什么，实现时就可以在一拍完成，如下图</font>    
    ![alt text](img/image-23.png#img80)   
    <font size=3>相关代码参考[1]</font>    


