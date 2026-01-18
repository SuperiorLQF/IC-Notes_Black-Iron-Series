# <span class="hl">Verdi-TCL</span>
[TOC]
???+ success "<font size=3>reference</font>" 
    [1]  [verdi tcl reference](https://iccircle.com/static/upload/img20241018151618.pdf) 

## 一、verdi tcl交互界面开启 
![alt text](img/image-39.png#img70)  
## 二、将脚本加入到菜单栏中  
如果我开发了几个tcl脚本，但每次要使用都要source一下再用，可以考虑将脚本加入到verdi菜单中，点击使用   
例如我有一个脚本`hello.tcl`  
现在编写一个`user_init.tcl`用于将`hello.tcl`以及后续开发的更多的脚本都加入到verdi菜单栏中  
![alt text](img/image-40.png#img80)   
然后在每次打开verdi时只需要source一次   
![alt text](img/image-41.png#img40)   
之后开任何一个波形都在菜单可以看到开发的脚本对应的按钮   
![alt text](img/image-42.png#img70)  
点击之后，成功执行hello脚本并打印     
![alt text](img/image-43.png#img20)
