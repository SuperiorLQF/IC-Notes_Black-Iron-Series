# <span class="hl warn">SVA</span>(SystemVerilog Assertion)
[TOC]
## 简介
<font color =ff6622 font size=4>SVA断言(**assert**)是用来描述设计属性(**design property**)的一种简洁方式。</font>使用SVA可以检查RTL行为是否符合该属性
<div class="hb">
当然SVA不是描述和检查属性的唯一方式</br>
仅使用SV也可以实现，但是更加晦涩（写起来难，代码阅读起来也难），很难直接根据代码看出预期的属性
</div>

断言分为<span class="btl">即时(immediate)断言</span>和<span class="btl">并行(concurrent)断言</span>
### 即时断言
在代码执行到断言语句是进行立即检查    
格式如下
```systemverilog
[assert  name]:assert (expr) 
    [pass_action]
[else]
    [fail_action]
```
除了第一行，剩下的称为<span class="btl">action block</span>，可以省略
<div class="hb warn">
<font color=red><b>即时断言只能在程序块中</b></font></br>
如always_comb、task、function等
</div>
举例如下
```sv
`ifdef MODULENAME_ASSERT_ON
always_comb begin
    a_checkAB:assert(A==B) 
        $display ("pass")
    else
        $fatal("assert %m failed");
end
`endif
```
上述代码注意点：    
1.使用<span class="btl">ASSERT宏开关</span>控制assertion的开启和关闭  
2.<span class="btl">`%m`</span>可以得到assert名  
3.失败的action block还可以用<span class="btl">`$display`或者``uvm_error`</span>等其他log函数
  
### 并行断言
检查一段时序关系，可以持续监控数个周期，独立于过程块执行     
格式如下
```systemverilog
[assert  name]:assert property(property_expr) 
    [pass_action]
[else]
    [fail_action]
```
从格式上来看，直接区别就是assert后跟上了<span class="btl">`property`</span>

