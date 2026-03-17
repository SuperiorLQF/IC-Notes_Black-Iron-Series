# 小工具

这里收录了一些实用的 IC 小工具。

## SVA 仿真工具

<div class="tool-container">
  <select id="tool-select" class="tool-select">
    <option value="">-- 请选择工具--</option>
    <option value="sva-sim">🚀 SVA 全功能仿真器</option>
  </select>
  <button onclick="openTool()" class="tool-btn">开启新标签页</button>
</div>

<script>
function openTool() {
  var select = document.getElementById('tool-select');
  var value = select.value;
  
  if (value === 'sva-sim') {
    // 使用 _blank 属性，并去掉宽高限制，即可强制在浏览器新标签页打开
    // 注意路径：使用 ../ 退回根目录寻找 html 文件
    window.open('../sva_sim.html', '_blank');
  } else {
    alert('⚠️ 请先在下拉菜单中选择一个工具！');
  }
}
</script>

<style>
/* 稍微美化了一下你的 UI，让它更契合 Material 主题的风格 */
.tool-container {
  display: flex;
  gap: 15px;
  align-items: center;
  margin: 20px 0;
  padding: 25px;
  background: #f8f9fa;
  border: 1px solid #e0e0e0;
  border-radius: 8px;
  box-shadow: 0 2px 4px rgba(0,0,0,0.05);
}
.tool-select {
  padding: 10px 15px;
  font-size: 15px;
  border: 2px solid #bdc3c7;
  border-radius: 6px;
  background: white;
  min-width: 250px;
  color: #2c3e50;
  outline: none;
  transition: 0.2s;
}
.tool-select:focus {
  border-color: #3498db;
}
.tool-btn {
  padding: 10px 24px;
  font-size: 15px;
  background-color: #673ab7; /* 契合你 yaml 里配置的 deep purple */
  color: white;
  border: none;
  border-radius: 6px;
  cursor: pointer;
  font-weight: bold;
  transition: 0.2s;
  box-shadow: 0 2px 4px rgba(103, 58, 183, 0.3);
}
.tool-btn:hover {
  background-color: #512da8;
  transform: translateY(-1px);
  box-shadow: 0 4px 6px rgba(103, 58, 183, 0.4);
}
</style>