# <span class="hl info">波前分配器</span>(Wavefront Allocator)
???+success "Reference"    
    [1]《片上互联网络》：路由器微架构章  

<span class="btlr">分配器</span>，定义为<span class="btl">将N个请求匹配到M个资源的模块</span>（当然，这些请求不一定会同时满足，可能允许一部分，再阻塞一部分）   
分配器常用于Interconnect、Rounter等互联设计中。    
分配器有2个常用术语和仲裁器相同，<b>req和gnt</b>    
<div class = "hb tip">
req代表分配器的输入，二维矩阵，$N\times M$或者$M\times N$，代表N个请求者分别对M个资源的请求情况<br>   
gnt代表分配器决策后的输出，二维矩阵，$N\times M$或者$M\times N$，代表N个请求者分别对M个资源的请求的回应情况<br>   
</div>
<div class = "hb warn">
注意，在此问题背景下，<span class="btlr">一个请求者最多只能申请到一个资源，但是它在请求中可以声明其想要的所有资源</span>。<br> 
表现为请求者的gnt向量是one-hot或全0<br> 
</div>

下面给出典型场景。   
有3个请求者，4个资源的分配场景，每个请求者可以申请最多4个资源，但是最多只能得到1个资源。  

在简单设计中最常见的分配实现办法就是2级仲裁，如下图。   
先在每个请求者局部完成一级仲裁（图中每个红圈代表参与仲裁，需要从中选出一个1），仲裁结束后，每个请求者只输出对一个资源的请求   
再经过crossbar完成二级仲裁，在多个请求者对统一资源请求时进行仲裁决策   
显而易见，这样做匹配效率低下，资源容易空闲。（如果换个顺序，先crossbar再仲裁，结果也相似，参考书本124页的例子）  
![alt text](img/image-32.png#img80)   

为了提高资源分配效率，提出了波前分配器 
TODO
