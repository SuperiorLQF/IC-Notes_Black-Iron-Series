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
    const edges = options.edges !== undefined ? options.edges : target?.data?.map(e => e.t);
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
function editorPoint(e) {
    const rect = waveContainer.getBoundingClientRect();
    return { x: e.clientX-rect.left, y:e.clientY-rect.top, t: pxToTime(e.clientX-rect.left+state.offsetX), row: getTrackIdxAtY(e.clientY-rect.top+state.offsetY-state.topMargin) };
}
function waveformEnd() {
    let end = 0;
    function walk(nodes) { nodes.forEach(n => n.type === 'group' ? walk(n.children) : n.data.forEach(e => end = Math.max(end, e.t))); }
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
    editorClipboard={duration:end-start, signals:editorSelection.ids.map(id=>findNodeAndParent(state.tree,id)?.node).filter(n=>n && n.type!=='group').map(sig=>({type:sig.type, data:[{t:0,val:getSignalValueAtTime(sig,start)},...sig.data.filter(e=>e.t>start && e.t<end).map(e=>({t:e.t-start,val:e.val}))]}))};
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
        if(insert) {retimeSignalAttachments(sig.id,time=>time>=start?time+editorClipboard.duration:time);sig.data.forEach(e=>{if(e.t>=start)e.t+=editorClipboard.duration;});}
        else sig.data=sig.data.filter(e=>e.t<start || e.t>end);
        sig.data.push(...editorClipboard.signals[i].data.map(e=>({t:start+e.t,val:e.val})));
        if(!sig.data.some(e=>Math.abs(e.t-end)<1e-6)) sig.data.push({t:end,val:tail});
        cleanUpEvents(sig);
    }); updateUI();
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
        if(e.button!==0 || !['VIEW','EDIT'].includes(state.mode) || state.subMode!=='NORMAL' || state.measureMode!=='IDLE' || state.arrowMode!=='IDLE')return;
        const p=editorPoint(e),track=state.flatTracks[p.row];
        if(e.altKey){e.preventDefault();e.stopImmediatePropagation();if(measurementCursors.length===2)measurementCursors=[];measurementCursors.push(snapEditorTime(p.t)??p.t);return;}
        if(!track || track.node.type==='group' || p.y<state.topMargin)return;
        if(e.shiftKey && state.mode==='VIEW'){e.preventDefault();e.stopImmediatePropagation();editorGesture={kind:'selection',row:p.row};editorSelection={a:snapEditorTime(p.t)??nearestSignalEdge(track.node,p.t),b:snapEditorTime(p.t)??nearestSignalEdge(track.node,p.t),ids:[track.node.id]};return;}
        // View only selects/navigates. Edge changes require explicit Edit mode.
        if(state.mode!=='EDIT' || !state.selectedIds.has(track.node.id))return;
        const center=track.centerY+state.topMargin-state.offsetY;
        if(Math.abs(p.y-center)>23)return;
        const edge=track.node.data.findIndex(ev=>ev.t>0 && Math.abs(timeToPx(ev.t-p.t))<7);
        if(edge>=0){e.preventDefault();e.stopImmediatePropagation();editorSelection=null;state.selectedIds=new Set([track.node.id]);editorGesture={kind:'edge',id:track.node.id,index:edge,before:JSON.parse(JSON.stringify(state.tree)),connectionsBefore:JSON.parse(JSON.stringify(state.connections)),measurementsBefore:JSON.parse(JSON.stringify(state.measurements)),cursorBefore:state.cursorT,startX:e.clientX,edges:findNodeAndParent(state.tree,state.snapTargetId)?.node.data?.map(ev=>ev.t)};}
    },true);
    window.addEventListener('mousemove',e=>{
        if(!editorGesture)return;
        const g=editorGesture,p=editorPoint(e);
        if(g.kind==='pan'){state.offsetX=Math.max(0,g.ox+g.x-e.clientX);state.offsetY=Math.max(0,g.oy+g.y-e.clientY);}
        if(g.kind==='selection') {editorSelection.b=snapEditorTime(p.t)??editorSelection.b;editorSelection.ids=state.flatTracks.slice(Math.min(g.row,Math.max(0,p.row)),Math.max(g.row,Math.max(0,p.row))+1).filter(t=>t.node.type!=='group').map(t=>t.node.id);state.selectedIds=new Set(editorSelection.ids);state.cursorT=nearestSignalEdge(getSelectedSignals()[0], Math.min(editorSelection.a,editorSelection.b));}
        if(g.kind==='edge' && Math.abs(e.clientX-g.startX)>2){const sig=findNodeAndParent(state.tree,g.id).node;const prev=sig.data[g.index-1].t,next=sig.data[g.index+1]?.t??Infinity;const t=snapEditorTime(p.t,{min:prev+1e-6,max:next-1e-6,edges:g.edges});if(t!==null && t>prev+1e-6 && t<next-1e-6){const oldTime=sig.data[g.index].t;retimeSignalAttachments(g.id,time=>Math.abs(time-oldTime)<=1e-6?t:time);sig.data[g.index].t=t;state.cursorT=t;}}
        if(g.kind==='pan')clampHorizontalOffset();
        e.stopImmediatePropagation();updateUI();
    },true);
    window.addEventListener('mouseup',()=>{if(!editorGesture)return;const g=editorGesture;editorGesture=null;if(g.kind==='edge'){const sig=findNodeAndParent(state.tree,g.id)?.node;if(sig)cleanUpEvents(sig);}updateUI();},true);

}
