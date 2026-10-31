// Project persistence and editing tools; waveform time is always expressed in ns.
let editorNeedsRender = true, editorBlinkPhase = -1;
const projectHistory = { entries: [], index: -1, saved: '', timer: null, initialized: false, replaying: false };
const BACKUP_KEY = 'digiwave.project.v1';
const transientFields = new Set(['absoluteRenderY', '_currentTIdx1', '_currentTIdx2', 'assignedLane', 'renderedHeight', 'currentFullWidth', 'zoomLevel', 'renderY', 'baseTimeWidth']);
function projectData() {
    return JSON.parse(JSON.stringify({ formatVersion: 1, tree: state.tree, texts: state.texts, measurements: state.measurements, connections: state.connections, scaleX: state.scaleX }, (k,v) => transientFields.has(k) ? undefined : v));
}
function projectSnapshot() { return JSON.stringify(projectData()); }
function projectIsDirty() { return projectHistory.initialized && projectSnapshot() !== projectHistory.saved; }
function updateSaveStatus(message) {
    const el = document.getElementById('saveStatus');
    el.textContent = message || (projectIsDirty() ? '未导出' : '已导出 / 初始状态');
    document.getElementById('undoButton').disabled = projectHistory.index <= 0;
    document.getElementById('redoButton').disabled = projectHistory.index >= projectHistory.entries.length - 1;
}
function writeBackup() {
    try { localStorage.setItem(BACKUP_KEY, JSON.stringify({ savedAt: Date.now(), project: projectData() })); updateSaveStatus(projectIsDirty() ? '已本地备份 · 未导出' : '已本地备份'); }
    catch (_) { updateSaveStatus('本地备份失败，请导出 JSON'); }
}
function initializeHistory(dirty = false) {
    projectHistory.initialized = true;
    const snapshot = projectSnapshot();
    projectHistory.entries = [snapshot]; projectHistory.index = 0;
    projectHistory.saved = dirty ? '' : snapshot;
    updateSaveStatus();
}
function checkpointProject() {
    if (!projectHistory.initialized || projectHistory.replaying || editorGesture) return;
    const snapshot = projectSnapshot();
    const previous = JSON.parse(projectHistory.entries[projectHistory.index]);
    const current = JSON.parse(snapshot);
    delete previous.scaleX; delete current.scaleX;
    if (JSON.stringify(current) === JSON.stringify(previous)) return;
    projectHistory.entries.splice(projectHistory.index + 1);
    projectHistory.entries.push(snapshot);
    if (projectHistory.entries.length > 100) projectHistory.entries.shift();
    projectHistory.index = projectHistory.entries.length - 1;
    clearTimeout(projectHistory.timer); projectHistory.timer = setTimeout(writeBackup, 400);
    updateSaveStatus();
}
function applyProject(data) {
    state.tree = data.tree; state.texts = data.texts || []; state.measurements = data.measurements || []; state.connections = data.connections || []; state.scaleX = data.scaleX || 10;
    state.selectedIds.clear(); state.selectedTextId = state.selectedMeasureId = state.selectedConnId = null;
    state.cursorT = 0; state.offsetX = state.offsetY = 0; state.mode = 'VIEW'; state.subMode = 'NORMAL'; state.pendingVal = null;
    state.snapTargetId = null; state.measureMode = state.arrowMode = 'IDLE'; state.tempMeasurePoint = state.tempArrowPoint = null;
    state.boundTrackId = null; editorSelection = null; editorGesture = null;
    document.querySelectorAll('.modal').forEach(el => el.style.display = 'none');
    busValueInput.blur(); textInputOverlay.style.display = 'none';
}
function travelHistory(delta) {
    const index = projectHistory.index + delta;
    if (index < 0 || index >= projectHistory.entries.length || editorGesture) return;
    projectHistory.replaying = true;
    applyProject(JSON.parse(projectHistory.entries[index])); projectHistory.index = index; updateUI();
    projectHistory.replaying = false; writeBackup(); updateSaveStatus();
}
function undoProject() { travelHistory(-1); }
function redoProject() { travelHistory(1); }
function markProjectSaved() { projectHistory.saved = projectSnapshot(); writeBackup(); updateSaveStatus(); }
function validateProject(input) {
    const data = JSON.parse(JSON.stringify(input));
    if (!data || !Array.isArray(data.tree) || (data.formatVersion != null && data.formatVersion !== 1)) throw new Error('不支持的工程格式');
    const ids = new Set();
    const finite = n => typeof n === 'number' && Number.isFinite(n);
    function walk(nodes, depth = 0) {
        if (depth > 32) throw new Error('分组嵌套过深');
        for (const n of nodes) {
            if (!n || typeof n.id !== 'string' || ids.has(n.id) || typeof n.name !== 'string' || !['group','single','multi'].includes(n.type)) throw new Error('信号结构或 ID 无效');
            ids.add(n.id);
            if (n.type === 'group') { if (!Array.isArray(n.children)) throw new Error('分组无效'); walk(n.children, depth + 1); }
            else {
                if (!Array.isArray(n.data)) throw new Error('波形数据无效');
                if (n.anchors != null && (!Array.isArray(n.anchors) || n.anchors.some(t => !finite(t) || t < 0) || new Set(n.anchors).size !== n.anchors.length)) throw new Error('信号锚点无效');
                let prev = -1;
                for (const ev of n.data) {
                    if (!finite(ev.t) || ev.t < 0 || ev.t <= prev || typeof ev.val !== 'string' || (n.type === 'single' && !/^[01xz]$/i.test(ev.val))) throw new Error('跳变时间或数值无效');
                    prev = ev.t;
                }
            }
        }
    }
    walk(data.tree);
    for (const name of ['texts','measurements','connections']) {
        if (data[name] == null) data[name] = [];
        if (!Array.isArray(data[name])) throw new Error('标注数据无效');
        for (const o of data[name]) {
            if (!o || typeof o.id !== 'string') throw new Error('标注无效');
            if (name === 'texts') {
                if (!ids.has(o.trackId) || !finite(o.t) || o.t < 0 || !finite(o.size) || o.size <= 0 || typeof o.text !== 'string' || (o.y != null && !finite(o.y))) throw new Error('文本无效');
            } else if (!ids.has(o.sigId1) || !ids.has(o.sigId2) || !finite(o.t1) || !finite(o.t2) || o.t1 < 0 || o.t2 < 0) throw new Error('标尺或连线无效');
        }
    }
    if (data.scaleX != null && (!finite(data.scaleX) || data.scaleX <= 0 || data.scaleX > 1000)) throw new Error('缩放比例无效');
    return data;
}
function restoreLocalProject(manual = false) {
    try {
        const raw = localStorage.getItem(BACKUP_KEY); if (!raw) { if (manual) alert('没有可恢复的本地备份'); return false; }
        const backup = JSON.parse(raw); const data = validateProject(backup.project);
        if (!confirm(`恢复 ${new Date(backup.savedAt).toLocaleString()} 的本地备份？${manual ? '将替换当前工程。' : ''}`)) return false;
        applyProject(data);
        if (projectHistory.initialized) updateUI(); else { initializeHistory(true); updateUI(); }
        return true;
    } catch (_) { if (manual) alert('本地备份不可用，请导入 JSON'); return false; }
}
function parseDuration(raw) {
    const match = String(raw).trim().match(/^(\d+(?:\.\d*)?|\.\d+)\s*(ps|ns|us|ms)?$/i);
    return match ? Number(match[1]) * ({ps:0.001, ns:1, us:1000, ms:1000000}[(match[2] || 'ns').toLowerCase()]) : NaN;
}
let editorGesture = null, editorSelection = null, editorClipboard = null, measurementCursors = [];
function snapEditorTime(t, options = {}) {
    const time = Math.max(0, t);
    const min = options.min ?? 0, max = options.max ?? Infinity;
    const target = findNodeAndParent(state.tree, state.snapTargetId)?.node;
    const edges = options.edges !== undefined ? options.edges : (target ? signalBoundaryTimes(target) : undefined);
    if (edges) {
        // Reference grids are mandatory, not just a 10-pixel proximity hint.
        const candidates = edges.filter(edge => edge >= min && edge <= max);
        return candidates.reduce((nearest, edge) => nearest === null || Math.abs(edge-time) < Math.abs(nearest-time) ? edge : nearest, null);
    }
    const step = Number(document.getElementById('gridStep').value);
    if (Number.isFinite(step) && step > 0) {
        const first = Math.ceil(min / step), last = Math.floor(max / step);
        if (first > last) return null;
        return Math.max(first, Math.min(last, Math.round(time / step))) * step;
    }
    return Math.max(min, Math.min(max, time));
}
// Endpoints are identified by signal + edge time, preserving existing JSON projects.
function retimeSignalAttachments(signalId, retime) {
    for (const annotation of [...state.connections, ...state.measurements]) {
        if (annotation.sigId1 === signalId) annotation.t1 = retime(annotation.t1);
        if (annotation.sigId2 === signalId) annotation.t2 = retime(annotation.t2);
    }
}
function preserveAnnotationAnchors(sig) {
    const boundaries=signalBoundaryTimes(sig), keep=[];
    for (const annotation of [...state.connections, ...state.measurements]) {
        for (const side of [1,2]) {
            const time=annotation['t'+side];
            if (annotation['sigId'+side]===sig.id && !boundaries.some(t=>Math.abs(t-time)<=1e-6)) keep.push(time);
        }
    }
    if (keep.length) sig.anchors=[...new Set([...(sig.anchors||[]),...keep])].sort((a,b)=>a-b);
}
function signalBoundaryTimes(sig) {
    return [...new Set([...(sig?.data || []).map(e => e.t), ...(sig?.anchors || [])])].sort((a,b) => a-b);
}
function signalEndpointY(track, time) {
    const isAnchor = track.node.anchors?.some(t => Math.abs(t-time) <= 1e-6);
    const val = getSignalValueAtTime(track.node, time);
    const dy = isAnchor && track.node.type === 'single' ? (val === '1' ? -14 : val === '0' ? 14 : 0) : 0;
    return track.centerY + state.topMargin + dy;
}
function retimeAnchors(sig, retime) {
    if (sig.anchors) sig.anchors = [...new Set(sig.anchors.map(retime))].sort((a,b)=>a-b);
}
function toggleAnchorMode() {
    if (!getSelectedSignals().length) return;
    if (state.mode === 'VIEW') state.mode = 'EDIT';
    if (state.mode !== 'EDIT') return;
    state.subMode = state.subMode === 'ANCHOR' ? 'NORMAL' : 'ANCHOR';
    updateUI();
}
function removeCurrentAnchor() {
    const sig = getSelectedSignals()[0];
    if (!sig?.anchors) return;
    const time=state.cursorT;
    const attached = item => (item.sigId1===sig.id && Math.abs(item.t1-time)<=1e-6) || (item.sigId2===sig.id && Math.abs(item.t2-time)<=1e-6);
    if(sig.anchors.some(t=>Math.abs(t-time)<=1e-6)) {state.connections=state.connections.filter(item=>!attached(item));state.measurements=state.measurements.filter(item=>!attached(item));}
    sig.anchors = sig.anchors.filter(t => Math.abs(t-time)>1e-6);
    if (!sig.anchors.length) delete sig.anchors;
    state.cursorT = nearestSignalEdge(sig,state.cursorT);updateUI();
}

function editorPoint(e) {
    const rect = waveContainer.getBoundingClientRect();
    return { x: e.clientX-rect.left, y:e.clientY-rect.top, t: pxToTime(e.clientX-rect.left+state.offsetX), row: getTrackIdxAtY(e.clientY-rect.top+state.offsetY-state.topMargin) };
}
function waveformEnd() {
    let end = 0;
    function walk(nodes) { nodes.forEach(n => n.type === 'group' ? walk(n.children) : signalBoundaryTimes(n).forEach(time => end = Math.max(end, time))); }
    walk(state.tree); return end;
}
// At maximum zoom-out the viewport spans at most 120% of the signal duration.
function minimumWaveformScale() {
    return Math.max(0.001, waveContainer.clientWidth / (Math.max(10, waveformEnd()) * 1.2));
}
function boundedWaveformScale(scale) {
    const minimum = minimumWaveformScale();
    return Math.max(minimum, Math.min(1000, scale));
}
function clampHorizontalOffset() {
    const limit = Math.max(0, Math.max(10, waveformEnd()) * 1.2 * state.scaleX - waveContainer.clientWidth);
    state.offsetX = Math.max(0, Math.min(state.offsetX, limit));
}
function fitWaveform() {
    // F always fits the complete project, even with a selected time range.
    state.scaleX = boundedWaveformScale(waveContainer.clientWidth / Math.max(10, waveformEnd()));
    state.offsetX = 0;
    updateUI();
}

function generateClock() {
    const name = document.getElementById('clockName');
    const names = new Set(state.flatTracks.map(t => t.node.name));
    let index = 1, candidate = 'clk';
    while (names.has(candidate)) candidate = `clk_${index++}`;
    name.value = candidate;
    document.getElementById('clockError').textContent = '';
    document.getElementById('clockModal').style.display = 'flex';
    name.focus(); name.select();
}
let nextClockId = 0;
function uniqueClockId() {
    let id;
    do { id = `s_${Date.now()}_${nextClockId++}`; } while (findNodeAndParent(state.tree, id));
    return id;
}
function clockTimeInput(id) {
    const value = document.getElementById(id).valueAsNumber;
    const unit = document.getElementById(id + 'Unit').value;
    return value * ({ps:0.001, ns:1, us:1000, ms:1000000}[unit]);
}
function confirmClock() {
    const period = clockTimeInput('clockPeriod');
    const duty = Number(document.getElementById('clockDuty').value) / 100;
    const count = Number(document.getElementById('clockCount').value);
    const start = clockTimeInput('clockStart');
    const end = start + period * count;
    if (!(period > 0 && duty > 0 && duty < 1 && Number.isInteger(count) && count > 0 && count <= 10000 && start >= 0 && Number.isFinite(end) && end > start && start + period*duty > start && start+period*duty < start+period)) {
        document.getElementById('clockError').textContent = 'Enter a valid period, duty cycle, cycle count and start time.';
        return;
    }
    // A clock is created as an ordinary editable binary signal, without a selection prerequisite.
    const sig = { id: uniqueClockId(), name: document.getElementById('clockName').value.trim() || 'clk', type: 'single', color: '#2ecc71', thickness: 2, data: [] };
    if (start > 0) sig.data.push({t:0, val:'0'});
    for (let i = 0; i < count; i++) sig.data.push({t:start+i*period, val:'1'}, {t:start+i*period+period*duty, val:'0'});
    sig.data.push({t:end, val:'z'});
    state.tree.push(sig);
    state.selectedIds = new Set([sig.id]); state.mode = 'VIEW'; state.subMode = 'NORMAL'; state.pendingVal = null; state.cursorT = start;
    editorSelection = null;
    updateUI();
    closeModal('clockModal');
    fitWaveform();
}

function copyEditorSelection() {
    if (!editorSelection || Math.abs(editorSelection.a-editorSelection.b)<1e-9) return;
    const start=Math.min(editorSelection.a,editorSelection.b), end=Math.max(editorSelection.a,editorSelection.b);
    editorClipboard={duration:end-start, signals:editorSelection.ids.map(id=>findNodeAndParent(state.tree,id)?.node).filter(n=>n && n.type!=='group').map(sig=>({type:sig.type, anchors:(sig.anchors||[]).filter(t=>t>=start && t<end).map(t=>t-start), data:[{t:0,val:getSignalValueAtTime(sig,start)},...sig.data.filter(e=>e.t>start && e.t<end).map(e=>({t:e.t-start,val:e.val}))]}))};
    updateSaveStatus('选区已复制（编辑器内部）');
}
function pasteEditorSelection(insert) {
    if (!editorClipboard) return;
    const sigs=getSelectedSignals();
    if (sigs.length!==editorClipboard.signals.length || sigs.some((s,i)=>s.type!==editorClipboard.signals[i].type)) { alert('请选择与复制源数量、类型一致的目标信号'); return; }
    const start=state.cursorT, end=start+editorClipboard.duration;
    if (!Number.isFinite(end)) { alert('粘贴时间超出范围'); return; }
    sigs.forEach((sig,i)=>{
        const tail=getSignalValueAtTime(sig,insert?start:end);
        if(insert) {retimeAnchors(sig,time=>time>=start?time+editorClipboard.duration:time);retimeSignalAttachments(sig.id,time=>time>=start?time+editorClipboard.duration:time);sig.data.forEach(e=>{if(e.t>=start)e.t+=editorClipboard.duration;});}
        else {sig.data=sig.data.filter(e=>e.t<start || e.t>end);if(sig.anchors)sig.anchors=sig.anchors.filter(t=>t<start || t>end);}
        const pastedAnchors=(editorClipboard.signals[i].anchors||[]).map(t=>start+t);
        if(pastedAnchors.length)sig.anchors=[...new Set([...(sig.anchors||[]),...pastedAnchors])].sort((a,b)=>a-b);
        sig.data.push(...editorClipboard.signals[i].data.map(e=>({t:start+e.t,val:e.val})));
        if(!sig.data.some(e=>Math.abs(e.t-end)<1e-6)) sig.data.push({t:end,val:tail});
        cleanUpEvents(sig);
    }); updateUI();
}
function updateEditorHelp() {
    const host = document.getElementById('editorHelp');
    if (!host) return;
    const expanded = host.querySelector('details')?.open || false;
    const sig = getSelectedSignals()[0];
    const isBus = sig?.type === 'multi';
    const editing = state.mode === 'EDIT', inserting = state.mode === 'INSERT';
    const actions = [];
    let title = state.mode;
    const add = (keys, text) => actions.push({keys: Array.isArray(keys) ? keys : [keys], text});
    if (durationModal.style.display === 'flex') {
        title = `${state.mode} · DURATION`;
        add('输入', '持续时间：数字，可带 ns / us / ms');add('↵ Enter', '确认持续时间并插入波形');
        add('⌫ Backspace', '删除时间输入中的字符');add('⎋ Esc', '关闭时间输入面板');
    } else if (state.measureMode !== 'IDLE' || state.arrowMode !== 'IDLE') {
        const measuring = state.measureMode !== 'IDLE';
        const mode = measuring ? state.measureMode : state.arrowMode;
        title = measuring ? 'MEASURE' : 'ARROW';
        add('鼠标', mode.endsWith('P1') ? '点击第一个信号边沿' : '点击第二个信号边沿');
        add(measuring ? 'M' : 'A', '取消当前工具');
    } else if (state.mode === 'TEXT') {
        add('鼠标', '选择绑定通道，点击添加文字；拖动注释移动');
        add('↵ Enter', '确认输入的注释');add('滚轮', '选中注释时调整字号');
        add('C', '注释属性 / 便签设置');add('Delete', '删除所选注释');add('⎋ Esc', '取消输入或返回 View');
    } else if (state.subMode === 'ANCHOR') {
        title = 'EDIT · ANCHOR';add('鼠标', '点击当前信号插入小竖线锚点，不改变电平');add('⎋ Esc', '取消放置锚点');
    } else if (state.subMode.startsWith('REPEAT')) {
        title = `${state.mode} · REPEAT`;
        if (state.subMode === 'REPEAT_START') add('鼠标', '选择片段起始边沿');
        else if (state.subMode === 'REPEAT_END') add('鼠标', '选择片段结束边沿，必须晚于起点');
        else { add('数字', '输入重复次数');add('↵ Enter', '确认重复'); }
        add('⎋ Esc', '取消片段选择；次数面板可点 Cancel');
        add('目标', inserting ? '在编辑光标处重复插入，后续波形后移' : '在编辑光标处重复覆盖，光标不移动');
    } else if ((editing || inserting) && state.subMode === 'VALUE') {
        title = `${state.mode} · BUS VALUE`;
        add('输入', '十进制 / 0x 十六进制 / X / Z');
        add('↵ Enter', inserting ? '打开持续时间面板，确认后插入' : '应用当前总线值并结束数值输入');
        if (inserting) add('␣ Space', '按参考信号下一边沿或上次时长插入');
        add('⌫ Backspace', '删除输入框中的字符，不删除波形');
        add('⎋ Esc', '退出数值输入，保留当前编辑模式');
    } else if ((editing || inserting) && sig) {
        title = `${state.mode} · ${isBus ? 'BUS' : 'BINARY'}`;
        if (isBus) { add('V', '打开总线数值输入框（十进制 / 0x 十六进制）');add(['X','Z'], '设置总线待写状态'); }
        else add(['0','1','X','Z'], '设置待写电平 / 状态（回车后应用）');
        add('↵ Enter', editing ? '修改光标所在波形段的值' : '输入持续时间，插入并后推后续波形');
        if (inserting) {
            add('␣ Space', '延续到参考信号下一边沿；无后续参考沿时复用上次时长');
            add('鼠标点击', '在光标右侧指定插入终点');
        } else add('鼠标拖动', '移动所选信号边沿；遵守网格吸附，连接线和标尺随动');
        add('⌫ Backspace', '删除光标与前一边沿之间的波形，后续内容前移');
        if (editing) {add('K', '点击放置独立锚点，可作为连线端点');add('Shift+K', '移除光标所在锚点');}
        add('R', inserting ? '选择片段并重复插入' : '选择片段并重复覆盖');
        add(['←','→'], '定位前后边沿');add('C', isBus ? '名称 / 颜色 / 线宽 / 总线进制属性' : '名称 / 颜色 / 线宽属性');
        add('⎋ Esc', '返回 View');
    } else if (editing || inserting) {
        title = `${state.mode} · 未选择信号`;
        add('⎋ Esc', '先返回 View，再选择要操作的信号');
    } else {
        title = 'VIEW';
        add('鼠标点击', '选择信号并定位最近边沿');add(['↑','↓'], '切换通道');add(['←','→'], '定位前后边沿');
        if (sig) { add('E', '修改电平 / 拖动边沿');add('I', '插入波形');add('K', '放置信号锚点');add('C', '打开属性'); }
        else add('开始', '先点击信号；或从加号菜单添加 Binary / Bus / Clock');
        add('Shift + 拖动', '跨通道框选时间范围');add('Ctrl + 点击', '多选通道');add('Ctrl+G', '将选中通道分组');
    }
    host.replaceChildren();
    const heading = document.createElement('strong');heading.className = 'help-mode';heading.textContent = title;host.append(heading);
    function appendActions(container, items) {
        for (const item of items) {
            const row = document.createElement('span');row.className = 'help-action';
            item.keys.forEach(key => {const kbd=document.createElement('kbd');kbd.textContent=key;row.append(kbd);});
            const label=document.createElement('span');label.textContent=item.text;row.append(label);container.append(row);
        }
    }
    const primary=document.createElement('div');primary.className='help-actions';appendActions(primary,actions);host.append(primary);
    if (!(state.subMode === 'VALUE' || state.subMode === 'REPEAT_MODAL' || durationModal.style.display === 'flex')) {
        const more=document.createElement('details');more.open=expanded;
        const summary=document.createElement('summary');summary.textContent='浏览、标注与通用操作';more.append(summary);
        const common=document.createElement('div');common.className='help-actions';
        appendActions(common,[
            {keys:['Ctrl/Cmd+Z'],text:'撤销'}, {keys:['Ctrl/Cmd+Shift+Z','Ctrl/Cmd+Y'],text:'重做'},
            {keys:['Ctrl/Cmd+C'],text:'复制已框选的波形'}, {keys:['Ctrl/Cmd+V'],text:'覆盖粘贴到选中通道的光标处'}, {keys:['Ctrl/Cmd+Shift+V'],text:'插入粘贴并后推内容'},
            {keys:['Delete'],text:'删除选中的信号 / 连线 / 标尺 / 注释'}, {keys:['F'],text:'水平适配全部波形'},
            {keys:['Ctrl + 滚轮'],text:'缩放时间轴'}, {keys:['滚轮'],text:'上下浏览通道'}, {keys:['Shift + 滚轮','中键拖动'],text:'平移视图'},
            {keys:['Alt + 点击'],text:'放置两个时间游标，显示 Δt'}, {keys:['M'],text:'边沿测量标尺'}, {keys:['A'],text:'边沿事件连线'}, {keys:['T'],text:'注释模式'}
        ]);more.append(common);host.append(more);
    }
}

function renderEditorOverlay() {
    const w=canvas.clientWidth, h=canvas.clientHeight;
    ctx.save();
    if(editorSelection) {
        const left=timeToPx(Math.min(editorSelection.a,editorSelection.b))-state.offsetX;
        const width=timeToPx(Math.abs(editorSelection.a-editorSelection.b));
        ctx.fillStyle=state.printMode?'rgba(0,0,0,.08)':'rgba(70,150,255,.18)'; ctx.strokeStyle=state.printMode?'#000':'#4696ff';
        state.flatTracks.filter(t=>editorSelection.ids.includes(t.node.id)).forEach(t=>{const y=t.yOffset+state.topMargin-state.offsetY;ctx.fillRect(left,y,width,t.height);ctx.strokeRect(left,y,width,t.height);});
    }
    ctx.fillStyle=getTheme().bg;ctx.fillRect(0,0,w,28);
    const raw=80/state.scaleX, power=10**Math.floor(Math.log10(raw)), ratio=raw/power;
    const step=(ratio<=1?1:ratio<=2?2:ratio<=5?5:10)*power;
    ctx.textAlign='left';ctx.textBaseline='alphabetic';
    ctx.font='11px Consolas, monospace';ctx.strokeStyle=state.printMode?'#000':'#777';ctx.fillStyle=state.printMode?'#000':'#bbb';
    for(let t=Math.ceil(pxToTime(state.offsetX)/step)*step;t<pxToTime(state.offsetX+w);t+=step) {const x=timeToPx(t)-state.offsetX;ctx.beginPath();ctx.moveTo(x,20);ctx.lineTo(x,28);ctx.stroke();ctx.fillText(`${Number(t.toPrecision(8))} ns`,x+3,15);}
    measurementCursors.forEach((t,i)=>{const x=timeToPx(t)-state.offsetX;ctx.strokeStyle=state.printMode?'#000':(i?'#fa5':'#5df');ctx.beginPath();ctx.moveTo(x,28);ctx.lineTo(x,h);ctx.stroke();});
    if(measurementCursors.length===2) {ctx.fillStyle=state.printMode?'#000':'#fff';ctx.fillText(`Δt ${Number(Math.abs(measurementCursors[1]-measurementCursors[0]).toPrecision(8))} ns`,10,h-12);}
    ctx.restore();
}
function installEditorInteractions() {
    document.getElementById('clockAddButton').addEventListener('click', confirmClock);
    document.getElementById('clockModal').addEventListener('submit', e => { e.preventDefault(); confirmClock(); });
    document.getElementById('clockModal').addEventListener('keydown', e => {
        if (e.key === 'Enter' && e.target.tagName === 'INPUT') { e.preventDefault(); e.stopPropagation(); confirmClock(); }
    });
    window.addEventListener('beforeunload', e=>{if(projectIsDirty()){writeBackup();e.preventDefault();e.returnValue='';}});
    document.addEventListener('visibilitychange',()=>{if(document.hidden && projectHistory.initialized)writeBackup();});
    window.addEventListener('keydown',e=>{
        if(['INPUT','TEXTAREA','SELECT'].includes(document.activeElement.tagName) || document.querySelector('.modal[style*="flex"]')) return;
        if(e.key.toLowerCase()==='k' && !e.ctrlKey && !e.metaKey && (state.mode==='VIEW'||state.mode==='EDIT')) {e.preventDefault();e.stopImmediatePropagation();if(e.shiftKey)removeCurrentAnchor();else toggleAnchorMode();return;}
        if(e.key.toLowerCase()==='f' && !e.ctrlKey && !e.metaKey && !e.altKey) {
            e.preventDefault();e.stopImmediatePropagation();fitWaveform();return;
        }
        if(e.ctrlKey || e.metaKey) {
            const k=e.key.toLowerCase();
            if(['z','y','c','v'].includes(k)) {
                e.preventDefault();e.stopImmediatePropagation();
                if(k==='z') e.shiftKey?redoProject():undoProject();
                if(k==='y')redoProject();
                if(k==='c')copyEditorSelection();
                if(k==='v')pasteEditorSelection(e.shiftKey);
            }
        }
        if(e.key==='Escape' && editorGesture) {
            if(editorGesture.before) {
                state.tree=editorGesture.before;
                state.connections=editorGesture.connectionsBefore;
                state.measurements=editorGesture.measurementsBefore;
                state.cursorT=editorGesture.cursorBefore;
            }
            editorGesture=null;updateUI();
        }
    },true);
    waveContainer.addEventListener('wheel',e=>{
        if(e.ctrlKey || (state.mode==='TEXT' && state.selectedTextId && !e.shiftKey))return;
        e.preventDefault();e.stopImmediatePropagation();
        if(e.shiftKey || Math.abs(e.deltaX)>Math.abs(e.deltaY)) state.offsetX=Math.max(0,state.offsetX+(e.deltaX||e.deltaY));
        else {const last=state.flatTracks.at(-1);const total=last?last.yOffset+last.height:0;state.offsetY=Math.max(0,Math.min(Math.max(0,total-waveContainer.clientHeight+state.topMargin),state.offsetY+e.deltaY));}
        clampHorizontalOffset();updateUI();
    },{capture:true,passive:false});
    waveContainer.addEventListener('mousedown',e=>{
        if(e.button===1) {e.preventDefault();e.stopImmediatePropagation();editorGesture={kind:'pan',x:e.clientX,y:e.clientY,ox:state.offsetX,oy:state.offsetY};return;}
        if(e.button===0 && state.mode==='EDIT' && state.subMode==='ANCHOR') {
            e.preventDefault();e.stopImmediatePropagation();
            const p=editorPoint(e),sig=getSelectedSignals()[0],track=state.flatTracks[p.row];
            if (!sig || track?.node.id!==sig.id || p.y<state.topMargin) return;
            const time=snapEditorTime(p.t);if(time===null)return;
            if (!signalBoundaryTimes(sig).some(t=>Math.abs(t-time)<=1e-6)) {sig.anchors=[...(sig.anchors||[]),time].sort((a,b)=>a-b);}
            state.cursorT=time;state.subMode='NORMAL';updateUI();return;
        }
        if(e.button!==0 || !['VIEW','EDIT'].includes(state.mode) || state.subMode!=='NORMAL' || state.measureMode!=='IDLE' || state.arrowMode!=='IDLE')return;
        const p=editorPoint(e),track=state.flatTracks[p.row];
        if(e.altKey){e.preventDefault();e.stopImmediatePropagation();if(measurementCursors.length===2)measurementCursors=[];measurementCursors.push(snapEditorTime(p.t)??p.t);return;}
        if(!track || track.node.type==='group' || p.y<state.topMargin)return;
        if(e.shiftKey && state.mode==='VIEW'){e.preventDefault();e.stopImmediatePropagation();editorGesture={kind:'selection',row:p.row};editorSelection={a:snapEditorTime(p.t)??nearestSignalEdge(track.node,p.t),b:snapEditorTime(p.t)??nearestSignalEdge(track.node,p.t),ids:[track.node.id]};return;}
        // View only selects/navigates. Edge changes require explicit Edit mode.
        if(state.mode!=='EDIT' || !state.selectedIds.has(track.node.id))return;
        const center=track.centerY+state.topMargin-state.offsetY;
        if(Math.abs(p.y-center)>23)return;
        const anchor=(track.node.anchors||[]).findIndex(t=>Math.abs(timeToPx(t-p.t))<7);
        const edge=track.node.data.findIndex(ev=>ev.t>0 && Math.abs(timeToPx(ev.t-p.t))<7);
        if(edge>=0 || anchor>=0){e.preventDefault();e.stopImmediatePropagation();editorSelection=null;state.selectedIds=new Set([track.node.id]);editorGesture={kind:'edge',id:track.node.id,index:anchor>=0?anchor:edge,isAnchor:anchor>=0,before:JSON.parse(JSON.stringify(state.tree)),connectionsBefore:JSON.parse(JSON.stringify(state.connections)),measurementsBefore:JSON.parse(JSON.stringify(state.measurements)),cursorBefore:state.cursorT,startX:e.clientX,edges:state.snapTargetId?signalBoundaryTimes(findNodeAndParent(state.tree,state.snapTargetId)?.node):undefined};}
    },true);
    window.addEventListener('mousemove',e=>{
        if(!editorGesture)return;
        const g=editorGesture,p=editorPoint(e);
        if(g.kind==='pan'){state.offsetX=Math.max(0,g.ox+g.x-e.clientX);state.offsetY=Math.max(0,g.oy+g.y-e.clientY);}
        if(g.kind==='selection') {editorSelection.b=snapEditorTime(p.t)??editorSelection.b;editorSelection.ids=state.flatTracks.slice(Math.min(g.row,Math.max(0,p.row)),Math.max(g.row,Math.max(0,p.row))+1).filter(t=>t.node.type!=='group').map(t=>t.node.id);state.selectedIds=new Set(editorSelection.ids);state.cursorT=nearestSignalEdge(getSelectedSignals()[0], Math.min(editorSelection.a,editorSelection.b));}
        if(g.kind==='edge' && Math.abs(e.clientX-g.startX)>2) {
            const sig=findNodeAndParent(state.tree,g.id).node;
            const oldTime=g.isAnchor?sig.anchors[g.index]:sig.data[g.index].t;
            const boundaries=signalBoundaryTimes(sig),index=boundaries.indexOf(oldTime);
            const prev=index>0?boundaries[index-1]:0,next=boundaries[index+1]??Infinity;
            const t=snapEditorTime(p.t,{min:prev+1e-6,max:next-1e-6,edges:g.edges});
            if(t!==null && t>prev+1e-6 && t<next-1e-6) {
                retimeSignalAttachments(g.id,time=>Math.abs(time-oldTime)<=1e-6?t:time);
                if(g.isAnchor)sig.anchors[g.index]=t;else sig.data[g.index].t=t;
                state.cursorT=t;
            }
        }
        if(g.kind==='pan')clampHorizontalOffset();
        e.stopImmediatePropagation();updateUI();
    },true);
    window.addEventListener('mouseup',()=>{if(!editorGesture)return;const g=editorGesture;editorGesture=null;if(g.kind==='edge'){const sig=findNodeAndParent(state.tree,g.id)?.node;if(sig)cleanUpEvents(sig);}updateUI();},true);

}
