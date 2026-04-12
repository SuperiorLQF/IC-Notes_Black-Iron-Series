let state = {
    scaleX: 10,     
    offsetX: 0,
    offsetY: 0,
    topMargin: 40,

    mode: 'VIEW',      
    subMode: 'NORMAL', 
    printMode: false,
    
    cursorT: 0,     
    pendingVal: null, 
    
    addingSignalType: null, 
    selectedIds: new Set(),
    snapTargetId: null,

    // Repeat 辅助
    hoverEdgeT: null,
    repeatStartT: null,
    repeatEndT: null,

    // 高级功能：测量标尺、连线、文本
    measureMode: 'IDLE', 
    measurements: [],
    selectedMeasureId: null,
    tempMeasurePoint: null,

    arrowMode: 'IDLE',   
    connections: [],
    selectedConnId: null,
    tempArrowPoint: null,
    dragArrowConnId: null,

    texts: [],
    selectedTextId: null,
    isEditingText: false,
    boundTrackId: null,

    flatTracks: [], // 带高度信息的扁平化数组

    // 默认全空
    tree: []
};

let lastDurationValue = "10"; 
let lastRepeatValue = "5";

// 新增独立的拖动状态变量
let isDraggingText = false; 
let dragOffset = { x: 0, y: 0 };

const canvas = document.getElementById('waveCanvas');
const ctx = canvas.getContext('2d');
const waveContainer = document.getElementById('waveContainer');
const durationModal = document.getElementById('durationModal');
const durationInput = document.getElementById('durationInput');
const repeatModal = document.getElementById('repeatModal');
const repeatInput = document.getElementById('repeatInput');
const attrModal = document.getElementById('attrModal');
const busValueInput = document.getElementById('busValueInput');
const textInputOverlay = document.getElementById('textInputOverlay');

// ================= 主题系统 =================
function getTheme() {
    let cursorBg = 'rgba(52, 152, 219, 0.3)';  
    let cursorLine = 'rgba(52, 152, 219, 1)';
    if (state.mode === 'EDIT') {
        cursorBg = 'rgba(192, 57, 43, 0.25)';   
        cursorLine = 'rgba(192, 57, 43, 0.9)';
    } else if (state.mode === 'INSERT') {
        cursorBg = 'rgba(230, 126, 34, 0.25)';  
        cursorLine = 'rgba(230, 126, 34, 0.9)';
    }
    
    if (state.printMode) {
        return {
            bg: '#ffffff', grid: '#dddddd', text: '#000000',
            cursorBg: 'rgba(0,0,0,0.05)', cursorLine: '#000000',
            xState: '#666666', zState: '#aaaaaa', measureBase: '#000000', tempMeasure: '#333333', 
            gapLine: '#555555', getSigColor: () => '#000000'
        };
    } else {
        return {
            bg: '#1e1e1e', 
            grid: 'rgba(255, 255, 255, 0.4)', // 【修改】大幅提高栅格亮度
            text: '#d4d4d4',
            cursorBg, cursorLine,
            xState: '#e74c3c', zState: '#7f8c8d', measureBase: null, tempMeasure: '#f1c40f', 
            gapLine: '#555555', getSigColor: (c) => c
        };
    }
}

// ================= 数据树与扁平化算法 =================
function updateFlatTracks() {
    let result = [];
    function traverse(nodes, depth) {
        nodes.forEach(node => {
            result.push({ node, depth });
            if (node.type === 'group' && node.expanded && node.children) traverse(node.children, depth + 1);
        });
    }
    traverse(state.tree, 0);
    state.flatTracks = result;
}

function findNodeAndParent(nodes, id, parent = null, index = -1) {
    for (let i = 0; i < nodes.length; i++) {
        if (nodes[i].id === id) return { node: nodes[i], parent, index: i, list: nodes };
        if (nodes[i].type === 'group' && nodes[i].children) {
            let res = findNodeAndParent(nodes[i].children, id, nodes[i], i);
            if (res) return res;
        }
    }
    return null;
}

function getSelectedSignals() {
    return state.flatTracks.filter(t => state.selectedIds.has(t.node.id) && t.node.type !== 'group').map(t => t.node);
}

function moveNode(dragId, dropId) {
    let srcInfo = findNodeAndParent(state.tree, dragId);
    if (!srcInfo) return;
    srcInfo.list.splice(srcInfo.index, 1);
    
    let dstInfo = findNodeAndParent(state.tree, dropId);
    if (!dstInfo) { state.tree.push(srcInfo.node); return; }

    if (dstInfo.node.type === 'group' && dstInfo.node.expanded) dstInfo.node.children.unshift(srcInfo.node); 
    else dstInfo.list.splice(dstInfo.index, 0, srcInfo.node); 
}

// ================= 动态高度与碰撞检测 =================
function computeTrackLayout() {
    state.flatTracks.forEach(t => { t.topSpace = 0; t.bottomSpace = 0; t.height = 60; });

    let trackIntervals = {};
    let activeMeasurements = [];
    state.measurements.forEach(m => m.absoluteRenderY = undefined);
    state.measurements.forEach(m => {
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === m.sigId1);
        const tIdx2 = state.flatTracks.findIndex(t => t.node.id === m.sigId2);
        if (tIdx1 === -1 || tIdx2 === -1) return; 
        m._currentTIdx1 = tIdx1; m._currentTIdx2 = tIdx2; activeMeasurements.push(m);
    });
    
    activeMeasurements.forEach(m => {
        const minTrackIdx = Math.min(m._currentTIdx1, m._currentTIdx2);
        if (!trackIntervals[minTrackIdx]) trackIntervals[minTrackIdx] = [];
        
        const absX1 = timeToPx(m.t1); const absX2 = timeToPx(m.t2);
        const pxWidth = Math.abs(absX2 - absX1);

        let textW = 0;
        if (pxWidth >= 35) {
            ctx.font = `14px Consolas, monospace`; textW = Math.min(ctx.measureText(m.text || 'Δt').width, pxWidth - 4); 
        } else if (pxWidth >= 10) textW = 6;

        trackIntervals[minTrackIdx].push({ m, min: Math.min(absX1, absX2) - textW/2 - 5, max: Math.max(absX1, absX2) + textW/2 + 5 });
    });

    for (let tIdx in trackIntervals) {
        let placed = []; let maxL = 0;
        trackIntervals[tIdx].sort((a,b) => a.min - b.min);
        trackIntervals[tIdx].forEach(inv => {
            let lane = 0; let collision = true;
            while(collision) {
                collision = false;
                for(let p of placed) if (p.lane === lane && inv.min < p.max && inv.max > p.min) { collision = true; break; }
                if (!collision) break; lane++;
            }
            placed.push({ ...inv, lane }); inv.m.assignedLane = lane; maxL = Math.max(maxL, lane);
        });
        state.flatTracks[tIdx].topSpace = Math.max(state.flatTracks[tIdx].topSpace, (maxL + 1) * 20);
    }

    let textsByTrack = {};
    state.texts.forEach(t => {
        if (!t.trackId) return;
        if (!textsByTrack[t.trackId]) textsByTrack[t.trackId] = [];
        textsByTrack[t.trackId].push(t);
        
        ctx.font = `${t.size}px Consolas, monospace`;
        let rawW = ctx.measureText(t.text || 'Note').width + (t.isSticky ? 28 : 8);
        let totalH = t.size;
        
        if (t.isSticky) {
            let lines = t.collapsed ? [] : (t.content || '').split('\n');
            if (!t.collapsed) {
                ctx.font = `${t.size * 0.85}px Consolas, monospace`;
                lines.forEach(l => { rawW = Math.max(rawW, ctx.measureText(l).width + 12); });
                totalH = t.size + 12 + (lines.length * t.size * 0.9);
                ctx.font = `${t.size}px Consolas, monospace`;
            } else { totalH = t.size + 4; }
        }
        t.renderedHeight = totalH;
        if (!t.baseScale) t.baseScale = state.scaleX;
        if (!t.baseTimeWidth) t.baseTimeWidth = pxToTime(rawW * (state.scaleX / t.baseScale));
        
        let strictPxWidth = timeToPx(t.baseTimeWidth);
        t.currentFullWidth = strictPxWidth;
        if (strictPxWidth < 6) t.zoomLevel = 3; else if (strictPxWidth < 25) t.zoomLevel = 2; else t.zoomLevel = 1;
    });

    for (let trkId in textsByTrack) {
        const track = state.flatTracks.find(tr => tr.node.id === trkId);
        if (!track) continue;

        let tList = textsByTrack[trkId];
        tList.sort((a, b) => a.y - b.y);

        let placedBelow = []; const WAVE_BOT = 20; 

        tList.forEach(t => {
            let currentY = Math.max(t.y || 0, WAVE_BOT + t.size); 
            let topEdge = currentY - t.size - 4;
            if (topEdge < WAVE_BOT) currentY += (WAVE_BOT - topEdge);
            
            let collision = true; let safety = 0;
            while (collision && safety < 50) {
                collision = false;
                for (let p of placedBelow) {
                    let tMinX = timeToPx(t.t); let tMaxX = tMinX + t.currentFullWidth;
                    let pMinX = timeToPx(p.t); let pMaxX = pMinX + p.currentFullWidth;
                    if (tMinX < pMaxX + 5 && tMaxX + 5 > pMinX) {
                        let tTop = currentY - t.size - 4;
                        let pBot = p.renderY - p.size + p.renderedHeight + 4;
                        if (tTop < pBot) { currentY += (pBot - tTop); collision = true; break; }
                    }
                }
                safety++;
            }
            t.renderY = currentY; placedBelow.push(t);
        });

        placedBelow.forEach(t => {
            let bottomEdge = t.renderY - t.size + t.renderedHeight + 4;
            if (bottomEdge > 20) track.bottomSpace = Math.max(track.bottomSpace, bottomEdge - 20);
        });
    }

    state.connections.forEach(conn => {
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === conn.sigId1);
        const tIdx2 = state.flatTracks.findIndex(t => t.node.id === conn.sigId2);
        if (tIdx1 !== -1 && tIdx1 === tIdx2) state.flatTracks[tIdx1].topSpace = Math.max(state.flatTracks[tIdx1].topSpace, 45); 
    });

    let currentY = 0;
    state.flatTracks.forEach(t => {
        t.height = 60 + t.topSpace + t.bottomSpace;
        t.yOffset = currentY;
        t.centerY = currentY + t.topSpace + 40; 
        currentY += t.height;
    });
}

function getTrackIdxAtY(y) {
    if (y < 0) return -1;
    let currentY = 0;
    for (let i = 0; i < state.flatTracks.length; i++) {
        let h = state.flatTracks[i].height;
        if (y >= currentY && y < currentY + h) return i;
        currentY += h;
    }
    return -1;
}

// ================= 基础运算运算 =================
function timeToPx(t) { return t * state.scaleX; }
function pxToTime(px) { return Math.max(0, px / state.scaleX); }

function getSignalValueAtTime(sig, t) {
    if (!sig.data || sig.data.length === 0) return 'z';
    let val = sig.data[0].val;
    for (let i = 0; i < sig.data.length; i++) {
        if (sig.data[i].t <= t + 1e-6) val = sig.data[i].val;
        else break;
    }
    return val;
}

function getEdges(sig, t) {
    let prev = 0, next = Infinity;
    if(!sig || !sig.data) return { prev, next };
    for (let e of sig.data) {
        if (e.t < t - 1e-6) prev = Math.max(prev, e.t);
        if (e.t > t + 1e-6) next = Math.min(next, e.t);
    }
    return { prev, next };
}

function parseDisplayStr(val, sig) {
    if (!val) return { str: 'z', isX: false, isZ: true };
    const lower = val.toLowerCase();
    if (lower === 'z') return { str: 'z', isX: false, isZ: true };
    if (lower === 'x') return { str: 'x', isX: true, isZ: false };
    
    let numVal = NaN;
    if (lower.startsWith('0x')) numVal = parseInt(val, 16);
    else if (/^-?\d+$/.test(val)) numVal = parseInt(val, 10);
    
    if (!isNaN(numVal)) {
        if (sig.radix === 'hex') return { str: '0x' + numVal.toString(16).toUpperCase(), isX:false, isZ:false };
        if (sig.radix === 'dec') return { str: numVal.toString(10), isX:false, isZ:false };
    }
    return { str: val, isX: false, isZ: false };
}

function togglePendingVal(sigs) {
    if (!sigs || sigs.length === 0) return;
    if (sigs[0].type === 'single') {
        if (state.pendingVal === '0') state.pendingVal = '1';
        else if (state.pendingVal === '1') state.pendingVal = '0';
    }
}

function applyDrawAction(sig, startT, duration, val) {
    if (state.mode === 'INSERT') insertAndPush(sig, startT, duration, val);
}

function insertAndPush(sig, startT, duration, val) {
    if (duration <= 0) return;
    let valAtStart = getSignalValueAtTime(sig, startT);

    sig.data.forEach(e => { if (e.t > startT + 1e-6) e.t += duration; });
    sig.data.forEach(e => { if (Math.abs(e.t - startT) <= 1e-6) e.t += duration; });
    sig.data.push({ t: startT, val: val });

    let hadEventAtEnd = sig.data.some(e => Math.abs(e.t - (startT + duration)) <= 1e-6);
    if (!hadEventAtEnd) sig.data.push({ t: startT + duration, val: valAtStart });
    cleanUpEvents(sig);
}

function editCurrentSegment(sig, t, newVal) {
    if (!sig.data || sig.data.length === 0) return;
    let targetIdx = -1;
    for (let i = sig.data.length - 1; i >= 0; i--) {
        if (sig.data[i].t <= t + 1e-6) { targetIdx = i; break; }
    }
    if (targetIdx !== -1) {
        sig.data[targetIdx].val = newVal;
        cleanUpEvents(sig); 
    }
}

function insertPatternAndPush(sig, insertT, startT, endT, count) {
    let patternDur = endT - startT;
    if (patternDur <= 0 || count <= 0) return;
    let pattern = [];
    pattern.push({ t: 0, val: getSignalValueAtTime(sig, startT) });
    sig.data.forEach(e => { if (e.t > startT + 1e-6 && e.t < endT - 1e-6) pattern.push({ t: e.t - startT, val: e.val }); });

    let totalPush = patternDur * count;
    let valAtInsert = getSignalValueAtTime(sig, insertT);

    sig.data.forEach(e => { if (e.t > insertT + 1e-6) e.t += totalPush; });
    sig.data.forEach(e => { if (Math.abs(e.t - insertT) <= 1e-6) e.t += totalPush; });

    for (let c = 0; c < count; c++) {
        let offset = insertT + c * patternDur;
        pattern.forEach(pe => { sig.data.push({ t: offset + pe.t, val: pe.val }); });
    }

    let hadEvEnd = sig.data.some(e => Math.abs(e.t - (insertT + totalPush)) <= 1e-6);
    if (!hadEvEnd) sig.data.push({ t: insertT + totalPush, val: valAtInsert });
    cleanUpEvents(sig);
}

function overwritePatternAndStay(sig, insertT, startT, endT, count) {
    let patternDur = endT - startT;
    if (patternDur <= 0 || count <= 0) return;
    let pattern = [];
    pattern.push({ t: 0, val: getSignalValueAtTime(sig, startT) });
    sig.data.forEach(e => { if (e.t > startT + 1e-6 && e.t < endT - 1e-6) pattern.push({ t: e.t - startT, val: e.val }); });

    let totalPush = patternDur * count;
    let endInsertT = insertT + totalPush;
    let valAtEnd = getSignalValueAtTime(sig, endInsertT);

    sig.data = sig.data.filter(e => e.t <= insertT + 1e-6 || e.t > endInsertT - 1e-6);
    sig.data = sig.data.filter(e => Math.abs(e.t - insertT) > 1e-6);

    for (let c = 0; c < count; c++) {
        let offset = insertT + c * patternDur;
        pattern.forEach(pe => { sig.data.push({ t: offset + pe.t, val: pe.val }); });
    }

    let hadEvEnd = sig.data.some(e => Math.abs(e.t - endInsertT) <= 1e-6);
    if (!hadEvEnd) sig.data.push({ t: endInsertT, val: valAtEnd });
    cleanUpEvents(sig);
}

function deleteAndPull(sig, startT, endT) {
    if (endT <= startT) return;
    let duration = endT - startT;
    sig.data = sig.data.filter(e => e.t <= startT + 1e-6 || e.t >= endT - 1e-6);
    sig.data.forEach(e => { if (e.t >= endT - 1e-6) e.t -= duration; });
    cleanUpEvents(sig);
}

function cleanUpEvents(sig) {
    sig.data.sort((a, b) => a.t - b.t);
    let cleaned = [];
    for (let i = 0; i < sig.data.length; i++) {
        if (i === 0 || sig.data[i].val !== sig.data[i-1].val) {
            if (cleaned.length > 0 && Math.abs(cleaned[cleaned.length-1].t - sig.data[i].t) <= 1e-6) {
                cleaned[cleaned.length-1].val = sig.data[i].val;
            } else { cleaned.push({...sig.data[i]}); }
        }
    }
    if (cleaned.length > 0 && cleaned[0].t > 1e-6) cleaned.unshift({t: 0, val: 'z'});
    sig.data = cleaned;
}

window.toggleGroup = function(id, e) {
    e.stopPropagation();
    let info = findNodeAndParent(state.tree, id);
    if (info && info.node.type === 'group') {
        info.node.expanded = !info.node.expanded;
        updateUI();
    }
}

window.ungroup = function(id, e) {
    e.stopPropagation();
    const info = findNodeAndParent(state.tree, id);
    if (!info) return;
    info.list.splice(info.index, 1, ...(info.node.children || []));
    if(state.selectedIds.has(id)) state.selectedIds.delete(id);
    updateUI();
}

function toggleMeasureMode() {
    state.measureMode = state.measureMode === 'IDLE' ? 'MEASURE_P1' : 'IDLE';
    state.tempMeasurePoint = null;
    const btn = document.getElementById('btnMeasure');
    if (state.measureMode !== 'IDLE') {
        if (btn) btn.classList.add('active');
        if (state.arrowMode !== 'IDLE') toggleArrowMode(); 
    } else { if (btn) btn.classList.remove('active'); }
    render();
}

function toggleArrowMode() {
    state.arrowMode = state.arrowMode === 'IDLE' ? 'ARROW_P1' : 'IDLE';
    state.tempArrowPoint = null;
    const btn = document.getElementById('btnArrow');
    if (state.arrowMode !== 'IDLE') {
        if (btn) btn.classList.add('active');
        if (state.measureMode !== 'IDLE') toggleMeasureMode(); 
    } else { if (btn) btn.classList.remove('active'); }
    render();
}

function togglePrintMode() {
    state.printMode = !state.printMode;
    const btn = document.getElementById('btnPrint');
    if (state.printMode) { document.body.classList.add('print-theme'); if(btn) btn.classList.add('active'); }
    else { document.body.classList.remove('print-theme'); if(btn) btn.classList.remove('active'); }
    render();
}

window.openScaleModal = function() {
    document.getElementById('scaleModal').style.display = 'flex';
    document.getElementById('scaleInput').value = Math.round(state.scaleX);
    setTimeout(() => { document.getElementById('scaleInput').focus(); document.getElementById('scaleInput').select(); }, 10);
};

window.applyScaleModal = function() {
    const val = parseFloat(document.getElementById('scaleInput').value);
    if (!isNaN(val) && val > 0) {
        state.scaleX = val;
        updateUI();
    }
    closeModal('scaleModal');
};

function updateSnapTarget() {
    state.snapTargetId = document.getElementById('snapSelect').value;
    render();
}

// ================= UI与渲染逻辑 =================

function resizeCanvas() {
    const rect = waveContainer.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    canvas.width = rect.width * dpr; canvas.height = rect.height * dpr;
    canvas.style.width = `${rect.width}px`; canvas.style.height = `${rect.height}px`;
    ctx.scale(dpr, dpr);
}
window.addEventListener('resize', resizeCanvas);

function updateUI() {
    updateFlatTracks();
    computeTrackLayout(); 
    
    const listEl = document.getElementById('signalList');
    listEl.innerHTML = '';
    
    state.flatTracks.forEach(track => {
        const sig = track.node;
        const row = document.createElement('div');
        
        let isSelected = state.selectedIds.has(sig.id);
        let isTextBound = (state.mode === 'TEXT' && state.boundTrackId === sig.id);
        
        row.className = `signal-row ${isSelected ? 'selected' : ''} ${isTextBound ? 'text-bound' : ''}`;
        row.style.height = `${track.height}px`;
        row.style.transform = `translateY(${-state.offsetY}px)`;
        row.style.paddingLeft = `${10 + track.depth * 15}px`;
        row.draggable = true;

        let iconHtml = '';
        if (sig.type === 'group') {
            iconHtml = `<span class="group-icon" onclick="toggleGroup('${sig.id}', event)">${sig.expanded ? '▼' : '▶'}</span>`;
        } else {
            iconHtml = `<div style="width:12px; height:12px; background:${state.printMode?'#000':sig.color}; border-radius:2px; flex-shrink:0; display:inline-block;"></div>`;
        }
        
        let innerHtml = `${iconHtml}<span class="signal-name">${sig.name} ${sig.type==='multi'? `[${sig.radix}]`:''}</span>`;
        if (sig.type === 'group') innerHtml += `<button class="ungroup-btn" onclick="ungroup('${sig.id}', event)">Ungroup</button>`;
        row.innerHTML = innerHtml;

        row.onclick = (e) => { 
            if (state.mode === 'TEXT') { state.boundTrackId = sig.id; updateUI(); return; }
            if (state.mode === 'VIEW') {
                if (e.ctrlKey) {
                    if (state.selectedIds.has(sig.id)) state.selectedIds.delete(sig.id);
                    else state.selectedIds.add(sig.id);
                } else {
                    state.selectedIds.clear(); state.selectedIds.add(sig.id);
                }
                state.cursorT = 0; updateUI(); 
            }
        };

        row.ondragstart = (e) => { e.dataTransfer.setData('text/plain', sig.id); };
        row.ondragover = (e) => { e.preventDefault(); row.classList.add('drag-over'); };
        row.ondragleave = (e) => { row.classList.remove('drag-over'); };
        row.ondrop = (e) => {
            e.preventDefault(); row.classList.remove('drag-over');
            const dragId = e.dataTransfer.getData('text/plain');
            if (dragId && dragId !== sig.id) { moveNode(dragId, sig.id); updateUI(); }
        };

        listEl.appendChild(row);
    });

    const snapSel = document.getElementById('snapSelect');
    const currentVal = snapSel.value;
    snapSel.innerHTML = '<option value="">None</option>';
    state.flatTracks.forEach(t => { if(t.node.type !== 'group') snapSel.innerHTML += `<option value="${t.node.id}">${t.node.name}</option>`; });
    if (findNodeAndParent(state.tree, currentVal)) snapSel.value = currentVal;

    const modeBtn = document.getElementById('statusMode');
    if (state.mode === 'TEXT') {
        const boundNode = findNodeAndParent(state.tree, state.boundTrackId);
        modeBtn.innerText = `LAYER: TEXT [${boundNode ? boundNode.node.name : 'None'}]`;
        modeBtn.className = 'mode-btn text-mode';
        waveContainer.style.cursor = 'default';
    } else {
        waveContainer.style.cursor = 'crosshair';
        if (state.subMode === 'REPEAT_START' || state.subMode === 'REPEAT_END' || state.subMode === 'REPEAT_MODAL') {
            modeBtn.innerText = 'REPEAT MODE'; modeBtn.className = 'mode-btn repeat-mode';
        } else {
            if (state.mode === 'INSERT') { modeBtn.innerText = 'INSERT MODE'; modeBtn.className = 'mode-btn insert-mode'; }
            else if (state.mode === 'EDIT') { modeBtn.innerText = 'EDIT MODE'; modeBtn.className = 'mode-btn edit-mode'; }
            else { modeBtn.innerText = 'VIEW MODE'; modeBtn.className = 'mode-btn view-mode'; }
        }
    }

    const cursorLabel = document.getElementById('statusCursor');
    if (state.subMode === 'REPEAT_START') cursorLabel.innerText = `[Repeat] 点击选择起点`;
    else if (state.subMode === 'REPEAT_END') cursorLabel.innerText = `[Repeat] 选择终点`;
    else if (state.subMode === 'REPEAT_MODAL') cursorLabel.innerText = `[Repeat] 配置重复次数`;
    else if (state.subMode === 'VALUE') cursorLabel.innerText = `[Value] 输入数值并回车`;
    else cursorLabel.innerText = `光标位置: ${state.cursorT.toFixed(2)} ns`;

    document.getElementById('statusZoom').innerText = `Scale: ${Math.round(state.scaleX)} px/ns`;
    const sigs = getSelectedSignals();
    document.getElementById('statusSelected').innerText = sigs.length > 0 ? `${sigs[0].name} ${sigs.length>1?'(Multiple)':''} selected` : '未选择信号';

    const mainSig = sigs[0];
    if (mainSig && mainSig.type === 'multi' && (state.mode === 'INSERT' || state.mode === 'EDIT') && state.subMode === 'VALUE') {
        busValueInput.style.display = 'inline-block';
        if (document.activeElement !== busValueInput) {
            busValueInput.value = (state.pendingVal === 'z' || state.pendingVal === 'x') ? '' : (state.pendingVal || '');
            busValueInput.focus(); busValueInput.select();
        }
    } else {
        busValueInput.style.display = 'none';
    }
    
    render(); 
}

function render() {
    const width = canvas.width; const height = canvas.height;
    const theme = getTheme();
    
    computeTrackLayout(); 

    const signalRows = document.getElementById('signalList').children;
    state.flatTracks.forEach((track, idx) => {
        if (signalRows[idx]) signalRows[idx].style.height = `${track.height}px`;
    });

    ctx.fillStyle = theme.bg; ctx.fillRect(0, 0, width, height);
    const rightMostVisibleT = pxToTime(state.offsetX + width);
    
    // 吸附线 (Measure/Arrow/Repeat)
    if (state.hoverEdgeT !== null && (state.subMode === 'REPEAT_START' || state.subMode === 'REPEAT_END' || state.arrowMode === 'ARROW_P2' || state.measureMode === 'MEASURE_P2')) {
        let px = timeToPx(state.hoverEdgeT) - state.offsetX;
        ctx.strokeStyle = '#e74c3c'; ctx.lineWidth = 1; ctx.setLineDash([5, 5]); ctx.beginPath();
        ctx.moveTo(px, 0); ctx.lineTo(px, height); ctx.stroke(); ctx.setLineDash([]);
    }

    // 绘制吸附栅格线
    if (state.snapTargetId) {
        const snapSigInfo = findNodeAndParent(state.tree, state.snapTargetId);
        if (snapSigInfo && snapSigInfo.node.type !== 'group') {
            ctx.strokeStyle = theme.grid; 
            ctx.lineWidth = 2;              // 【修改】线宽从 1 加粗到 2
            ctx.setLineDash([4, 4]);        // 【修改】虚线间距调大，更加清晰
            ctx.beginPath();
            snapSigInfo.node.data.forEach(e => {
                let px = timeToPx(e.t) - state.offsetX;
                if(px >= 0 && px <= width) { 
                    ctx.moveTo(px, 0); ctx.lineTo(px, height); 
                }
            });
            ctx.stroke(); ctx.setLineDash([]);
        }
    }

    state.flatTracks.forEach(track => {
        const sig = track.node;
        const absTop = track.yOffset - state.offsetY + state.topMargin;
        if (absTop > height || absTop + track.height < 0) return;

        if (state.mode === 'TEXT' && state.boundTrackId === sig.id) {
            ctx.fillStyle = state.printMode ? 'rgba(0,0,0,0.05)' : 'rgba(155, 89, 182, 0.25)';
            ctx.fillRect(0, absTop, width, track.height);
        } else if (state.selectedIds.has(sig.id)) {
            ctx.fillStyle = state.printMode ? 'rgba(0,0,0,0.03)' : 'rgba(52, 152, 219, 0.15)';
            ctx.fillRect(0, absTop, width, track.height);
        }

        const yMid = track.centerY - state.offsetY + state.topMargin; 
        const yHigh = yMid - 14, yLow = yMid + 14; 

        if (sig.type === 'group') {
            ctx.strokeStyle = theme.gapLine; ctx.lineWidth = 2; ctx.beginPath();
            ctx.moveTo(0, yMid); ctx.lineTo(width, yMid); ctx.stroke();
            return; 
        }

        if (state.selectedIds.has(sig.id) && state.mode !== 'TEXT') {
            if (state.subMode === 'REPEAT_END' && state.repeatStartT !== null) {
                const startPx = timeToPx(state.repeatStartT) - state.offsetX;
                ctx.strokeStyle = '#f39c12'; ctx.lineWidth = 4;
                ctx.beginPath(); ctx.moveTo(startPx, yHigh - 4); ctx.lineTo(startPx, yLow + 4); ctx.stroke();
            } else if (state.subMode === 'REPEAT_MODAL' && state.repeatStartT !== null && state.repeatEndT !== null) {
                const startPx = timeToPx(state.repeatStartT) - state.offsetX;
                const endPx = timeToPx(state.repeatEndT) - state.offsetX;
                ctx.fillStyle = 'rgba(243, 156, 18, 0.3)';
                ctx.fillRect(startPx, yHigh - 4, endPx - startPx, yLow - yHigh + 8);
                ctx.strokeStyle = '#f39c12'; ctx.lineWidth = 2;
                ctx.strokeRect(startPx, yHigh - 4, endPx - startPx, yLow - yHigh + 8);
            }
        }
        
        ctx.strokeStyle = theme.getSigColor(sig.color); ctx.lineWidth = sig.thickness || 2; 
        let events = sig.data || []; if (events.length === 0) events = [{t:0, val:'z'}];
        
        if (sig.type === 'single') {
            ctx.beginPath();
            let lastY = yMid; ctx.moveTo(timeToPx(0) - state.offsetX, lastY);
            for (let i = 0; i < events.length; i++) {
                const curT = events[i].t;
                const nextT = (i + 1 < events.length) ? events[i+1].t : rightMostVisibleT + 100; 
                const val = events[i].val;
                const startX = timeToPx(curT) - state.offsetX; 
                const endX = timeToPx(nextT) - state.offsetX;
                
                if (val === '1' || val === '0') {
                    let y = (val === '1') ? yHigh : yLow;
                    ctx.lineTo(startX, y); ctx.lineTo(endX, y); lastY = y;
                } else if (val === 'z') {
                    ctx.lineTo(startX, yMid); ctx.stroke(); ctx.beginPath(); 
                    ctx.strokeStyle = theme.zState; ctx.moveTo(startX, yMid); ctx.lineTo(endX, yMid); ctx.stroke();
                    ctx.beginPath(); ctx.strokeStyle = theme.getSigColor(sig.color); ctx.moveTo(endX, yMid); lastY = yMid;
                } else if (val === 'x') {
                    ctx.lineTo(startX, yMid); ctx.stroke(); ctx.beginPath();
                    ctx.strokeStyle = theme.xState; ctx.fillStyle = 'rgba(231, 76, 60, 0.25)'; 
                    ctx.rect(startX, yHigh, endX - startX, yLow - yHigh);
                    ctx.fill(); ctx.stroke();
                    ctx.save(); ctx.beginPath(); ctx.rect(startX, yHigh, endX - startX, yLow - yHigh); ctx.clip();
                    ctx.beginPath(); ctx.strokeStyle = 'rgba(231, 76, 60, 0.6)'; ctx.lineWidth = 1;
                    for (let lx = startX - 20; lx < endX; lx += 8) { ctx.moveTo(lx, yLow); ctx.lineTo(lx + 12, yHigh); }
                    ctx.stroke(); ctx.restore();
                    ctx.beginPath(); ctx.strokeStyle = theme.getSigColor(sig.color); ctx.moveTo(endX, yMid); lastY = yMid;
                }
            }
            ctx.stroke();
        } else if (sig.type === 'multi') {
            for (let i = 0; i < events.length; i++) {
                const curT = events[i].t;
                const nextT = (i + 1 < events.length) ? events[i+1].t : rightMostVisibleT + 100; 
                const val = events[i].val;
                const startX = timeToPx(curT) - state.offsetX; 
                const endX = timeToPx(nextT) - state.offsetX;
                const boxWidth = endX - startX;
                if (boxWidth <= 0 || startX > width || endX < 0) continue;

                const parsed = parseDisplayStr(val, sig);
                
                if (parsed.isZ) {
                    ctx.beginPath(); ctx.lineWidth = sig.thickness || 2;
                    ctx.moveTo(startX, yMid); ctx.lineTo(endX, yMid);
                    ctx.strokeStyle = theme.zState; ctx.stroke();
                } else {
                    const slope = Math.min(6, boxWidth / 2);
                    ctx.beginPath(); ctx.lineJoin = 'bevel'; ctx.lineWidth = sig.thickness || 2;
                    ctx.moveTo(startX, yMid); ctx.lineTo(startX + slope, yHigh); ctx.lineTo(endX - slope, yHigh);
                    ctx.lineTo(endX, yMid); ctx.lineTo(endX - slope, yLow); ctx.lineTo(startX + slope, yLow); ctx.closePath();

                    if (parsed.isX) {
                        ctx.strokeStyle = theme.xState; ctx.stroke();
                        ctx.save(); ctx.clip(); ctx.beginPath(); ctx.strokeStyle = 'rgba(231, 76, 60, 0.6)'; ctx.lineWidth = 1;
                        for (let lx = startX - 20; lx < endX; lx += 8) { ctx.moveTo(lx, yLow); ctx.lineTo(lx + 12, yHigh); }
                        ctx.stroke(); ctx.restore();
                    } else {
                        ctx.strokeStyle = theme.getSigColor(sig.color); ctx.stroke();
                        ctx.fillStyle = theme.getSigColor(sig.color); ctx.font = '12px Consolas, monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
                        let dispStr = parsed.str; let maxW = boxWidth - slope * 2 - 4;
                        if (maxW > 10) {
                            if (ctx.measureText(dispStr).width > maxW) {
                                while(dispStr.length>0 && ctx.measureText(dispStr+'..').width > maxW) dispStr = dispStr.slice(0,-1);
                                ctx.fillText(dispStr+'..', startX + boxWidth/2, yMid);
                            } else { ctx.fillText(dispStr, startX + boxWidth/2, yMid); }
                        }
                    }
                }
            }
        }

        const isP1Track = (state.measureMode === 'MEASURE_P2' && state.tempMeasurePoint && state.tempMeasurePoint.sigId === sig.id) ||
                          (state.arrowMode === 'ARROW_P2' && state.tempArrowPoint && state.tempArrowPoint.sigId === sig.id);

        if (isP1Track) {
            const p1T = state.measureMode === 'MEASURE_P2' ? state.tempMeasurePoint.t : state.tempArrowPoint.t;
            const p1Px = timeToPx(p1T) - state.offsetX;
            ctx.strokeStyle = '#3498db'; ctx.lineWidth = 4; ctx.beginPath();
            ctx.moveTo(p1Px, yHigh - 4); ctx.lineTo(p1Px, yLow + 4); ctx.stroke();
        }

        if (state.selectedIds.has(sig.id) && state.mode !== 'TEXT') {
            const cursorPxX = timeToPx(state.cursorT) - state.offsetX;
            const cursorWidth = 10;
            
            let showCursor = (state.mode === 'VIEW') ? true : (Math.floor(Date.now() / 500) % 2 === 0);

            if (showCursor) {
                ctx.fillStyle = theme.cursorBg;
                ctx.strokeStyle = theme.cursorLine;
                ctx.lineWidth = 1;
                ctx.fillRect(cursorPxX, yHigh - 6, cursorWidth, yLow - yHigh + 12);
                ctx.strokeRect(cursorPxX, yHigh - 6, cursorWidth, yLow - yHigh + 12);
            }

            if (state.pendingVal && (state.subMode === 'NORMAL' || state.subMode === 'VALUE') && (state.mode === 'INSERT' || state.mode === 'EDIT')) {
                const infoY = yLow + 18; 
                const drawX = cursorPxX;
                const iconX = drawX + 16;
                
                ctx.font = 'bold 12px "Consolas", monospace';
                ctx.fillStyle = '#f1c40f';
                ctx.strokeStyle = '#f1c40f';
                ctx.lineWidth = 2;
                ctx.textAlign = 'left';

                if (sig.type === 'single') {
                    const valMap = { '1': 'H', '0': 'L', 'x': 'X', 'z': 'Z' };
                    ctx.fillText(valMap[state.pendingVal] || '', drawX, infoY);
                    ctx.beginPath();
                    if (state.pendingVal === '1') { ctx.moveTo(iconX, infoY - 8); ctx.lineTo(iconX + 12, infoY - 8); }
                    else if (state.pendingVal === '0') { ctx.moveTo(iconX, infoY); ctx.lineTo(iconX + 12, infoY); }
                    else if (state.pendingVal === 'z') { ctx.moveTo(iconX, infoY - 4); ctx.lineTo(iconX + 12, infoY - 4); }
                    else if (state.pendingVal === 'x') { ctx.rect(iconX, infoY - 8, 12, 8); ctx.moveTo(iconX, infoY - 8); ctx.lineTo(iconX + 12, infoY); }
                    ctx.stroke();
                } else if (sig.type === 'multi') {
                    ctx.fillText(state.pendingVal.substring(0, 10), drawX, infoY);
                }
            }
        }
    });

    state.measurements.forEach(m => {
        if (m._currentTIdx1 === undefined || m._currentTIdx2 === undefined) return;
        const track1 = state.flatTracks[m._currentTIdx1]; const track2 = state.flatTracks[m._currentTIdx2];
        const minTrack = m._currentTIdx1 < m._currentTIdx2 ? track1 : track2;
        
        const px1 = timeToPx(m.t1) - state.offsetX; const px2 = timeToPx(m.t2) - state.offsetX;
        const pxWidth = Math.abs(px2 - px1); if (pxWidth < 3) return;

        m.absoluteRenderY = minTrack.centerY - 26 - (m.assignedLane * 20);
        const py1 = track1.centerY - state.offsetY + state.topMargin; const py2 = track2.centerY - state.offsetY + state.topMargin;
        const isSelected = (state.selectedMeasureId === m.id);

        const drawColor = theme.measureBase || m.color; 
        ctx.strokeStyle = drawColor; ctx.fillStyle = drawColor; ctx.lineWidth = isSelected ? m.thickness + 1 : m.thickness;

        const midY = m.absoluteRenderY - state.offsetY + state.topMargin; 

        if (pxWidth >= 20) {
            ctx.setLineDash([4, 4]); ctx.beginPath();
            ctx.moveTo(px1, py1); ctx.lineTo(px1, midY); ctx.moveTo(px2, py2); ctx.lineTo(px2, midY); ctx.stroke();
        }
        ctx.setLineDash([]); ctx.beginPath(); ctx.moveTo(px1, midY); ctx.lineTo(px2, midY); ctx.stroke();

        if (pxWidth >= 25) {
            const head = Math.min(10, pxWidth / 3); ctx.beginPath();
            const leftX = Math.min(px1, px2); const rightX = Math.max(px1, px2);
            if (m.arrowType !== 'one-way') {
                ctx.moveTo(leftX, midY); ctx.lineTo(leftX + head, midY - 3); ctx.moveTo(leftX, midY); ctx.lineTo(leftX + head, midY + 3);
            }
            ctx.moveTo(rightX, midY); ctx.lineTo(rightX - head, midY - 3); ctx.moveTo(rightX, midY); ctx.lineTo(rightX - head, midY + 3);
            ctx.stroke();
        }

        if (pxWidth >= 35) {
            ctx.font = (isSelected ? "bold " : "") + `14px Consolas, monospace`; ctx.textAlign = "center"; ctx.textBaseline = "bottom";
            let dtText = m.text || 'Δt'; let maxW = pxWidth - 4;
            if (ctx.measureText(dtText).width > maxW) {
                while (dtText.length > 0 && ctx.measureText(dtText + '...').width > maxW) dtText = dtText.slice(0, -1);
                if(dtText.length > 0) dtText += '...';
            }
            ctx.fillText(dtText, (px1 + px2) / 2, midY - 2);
        } else if (pxWidth >= 10) ctx.fillRect((px1+px2)/2 - 3, midY - 3, 6, 6);
    });

    state.connections.forEach(conn => {
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === conn.sigId1);
        const tIdx2 = state.flatTracks.findIndex(t => t.node.id === conn.sigId2);
        if (tIdx1 === -1 || tIdx2 === -1) return;

        const py1 = state.flatTracks[tIdx1].centerY - state.offsetY + state.topMargin;
        const py2 = state.flatTracks[tIdx2].centerY - state.offsetY + state.topMargin;
        const px1 = timeToPx(conn.t1) - state.offsetX; const px2 = timeToPx(conn.t2) - state.offsetX;

        const isSelected = (state.selectedConnId === conn.id);
        const drawColor = state.printMode ? '#000000' : (conn.color || '#e74c3c');

        let cpx = px1 + (px2 - px1) / 2; let cpy = (tIdx1 === tIdx2) ? py1 - 60 : py1;
        const lineDist = Math.sqrt((px2 - px1)**2 + (py2 - py1)**2);
        if (lineDist < 15) return; 

        ctx.strokeStyle = drawColor; ctx.fillStyle = drawColor; ctx.lineWidth = isSelected ? conn.thickness + 1 : conn.thickness;
        ctx.beginPath(); ctx.moveTo(px1, py1); ctx.quadraticCurveTo(cpx, cpy, px2, py2); ctx.stroke();

        const arrowLen = 8; const angle = Math.atan2(py2 - cpy, px2 - cpx); 
        ctx.beginPath(); ctx.moveTo(px2, py2);
        ctx.lineTo(px2 - arrowLen * Math.cos(angle - Math.PI/7), py2 - arrowLen * Math.sin(angle - Math.PI/7));
        ctx.lineTo(px2 - arrowLen * Math.cos(angle + Math.PI/7), py2 - arrowLen * Math.sin(angle + Math.PI/7));
        ctx.fill();

        if (lineDist >= 45 && conn.text) {
            const tParam = conn.textPos !== undefined ? conn.textPos : 0.5; const invT = 1 - tParam;
            const textX = invT * invT * px1 + 2 * invT * tParam * cpx + tParam * tParam * px2;
            const textY = invT * invT * py1 + 2 * invT * tParam * cpy + tParam * tParam * py2;
            
            ctx.font = (isSelected ? "bold " : "") + `12px Consolas, monospace`; ctx.textAlign = "center"; ctx.textBaseline = "middle"; 
            let dispText = conn.text; const maxW = lineDist - 10;
            if (ctx.measureText(dispText).width > maxW) {
                while (dispText.length > 0 && ctx.measureText(dispText + '...').width > maxW) dispText = dispText.slice(0, -1);
                if(dispText.length > 0) dispText += '...';
            }
            ctx.lineWidth = 4; ctx.strokeStyle = theme.bg; ctx.strokeText(dispText, textX, textY);
            ctx.fillStyle = drawColor; ctx.fillText(dispText, textX, textY);
        }
    });

    state.texts.forEach(t => {
        const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
        if (!track) return; 

        const screenX = timeToPx(t.t) - state.offsetX;
        const screenY = track.centerY + t.renderY - state.offsetY + state.topMargin;
        const boxPx = t.currentFullWidth; 
        const dSize = t.size; const totalH = t.renderedHeight;  

        if (state.mode === 'TEXT' && state.selectedTextId === t.id) {
            ctx.strokeStyle = theme.cursorLine; ctx.lineWidth = 1; ctx.setLineDash([4, 4]);
            ctx.strokeRect(screenX - 2, screenY - dSize - 6, boxPx + 4, totalH + 8); ctx.setLineDash([]);
        }
        if (t.zoomLevel === 3) return; 

        if (t.zoomLevel === 2) {
            if (t.isSticky) {
                ctx.fillStyle = state.printMode ? '#ffffff' : (t.bgColor || '#2d2d30');
                ctx.strokeStyle = state.printMode ? '#000000' : (t.color || '#f1c40f');
                ctx.fillRect(screenX, screenY - dSize - 4, boxPx, totalH + 4); ctx.strokeRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);
            } else {
                ctx.fillStyle = state.printMode ? '#000000' : t.color;
                ctx.fillRect(screenX, screenY - dSize, boxPx, totalH);
            }
            return;
        }

        let displayStr = t.text || 'Note';
        if (t.isSticky) {
            let lines = t.collapsed ? [] : (t.content || '').split('\n');
            ctx.fillStyle = state.printMode ? '#ffffff' : (t.bgColor || '#2d2d30');
            ctx.strokeStyle = state.printMode ? '#000000' : (t.color || '#f1c40f'); ctx.lineWidth = 1;
            ctx.fillRect(screenX, screenY - dSize - 4, boxPx, totalH + 4); ctx.strokeRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);

            if (boxPx >= 20) {
                ctx.fillStyle = state.printMode ? '#000000' : (t.color || '#f1c40f'); ctx.beginPath();
                if (t.collapsed) {
                    ctx.moveTo(screenX + 6, screenY - dSize/2 - 4); ctx.lineTo(screenX + 6, screenY - dSize/2 + 4); ctx.lineTo(screenX + 12, screenY - dSize/2);
                } else {
                    ctx.moveTo(screenX + 4, screenY - dSize/2 - 2); ctx.lineTo(screenX + 14, screenY - dSize/2 - 2); ctx.lineTo(screenX + 9, screenY - dSize/2 + 4);
                }
                ctx.fill();
            }

            ctx.font = `${dSize}px Consolas, monospace`; let titleStr = displayStr; let availableTitleW = boxPx - 20; 
            if (availableTitleW > 0) {
                if (ctx.measureText(titleStr).width > availableTitleW) {
                    while (titleStr.length > 0 && ctx.measureText(titleStr + '...').width > availableTitleW) titleStr = titleStr.slice(0, -1);
                    if (titleStr.length > 0 || availableTitleW > 15) titleStr += '...';
                }
                ctx.fillStyle = state.printMode ? '#000000' : (t.color || '#f1c40f'); ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
                ctx.fillText(titleStr, screenX + 18, screenY);
            }

            if (!t.collapsed) {
                ctx.fillStyle = state.printMode ? '#333333' : theme.text; ctx.font = `${dSize * 0.85}px Consolas, monospace`;
                lines.forEach((l, i) => {
                    let lineStr = l; let availableLineW = boxPx - 10;
                    if (availableLineW > 0) {
                        if (ctx.measureText(lineStr).width > availableLineW) {
                            while (lineStr.length > 0 && ctx.measureText(lineStr + '...').width > availableLineW) lineStr = lineStr.slice(0, -1);
                            if (lineStr.length > 0) lineStr += '...';
                        }
                        ctx.fillText(lineStr, screenX + 6, screenY + dSize + (i * dSize * 0.9));
                    }
                });
            }
        } else {
            ctx.font = `${dSize}px Consolas, monospace`; ctx.fillStyle = state.printMode ? '#000000' : t.color;
            ctx.textAlign = 'left'; ctx.textBaseline = 'bottom'; let availableW = boxPx - 4; 
            if (availableW > 0) {
                if (ctx.measureText(displayStr).width > availableW) {
                    while (displayStr.length > 0 && ctx.measureText(displayStr + '...').width > availableW) displayStr = displayStr.slice(0, -1);
                    if(displayStr.length > 0) displayStr += '...';
                }
                ctx.fillText(displayStr, screenX, screenY);
            }
        }
    });
}

function loop() { render(); requestAnimationFrame(loop); }

// ================= 交互响应与高级模式支持 =================

waveContainer.addEventListener('mousemove', (e) => {
    const rect = waveContainer.getBoundingClientRect();
    const mx = e.clientX - rect.left + state.offsetX;
    const my = e.clientY - rect.top + state.offsetY; 

    if (state.dragArrowConnId) {
        const conn = state.connections.find(c => c.id === state.dragArrowConnId);
        if (conn) {
            const tIdx1 = state.flatTracks.findIndex(t => t.node.id === conn.sigId1);
            const tIdx2 = state.flatTracks.findIndex(t => t.node.id === conn.sigId2);
            if (tIdx1 !== -1 && tIdx2 !== -1) {
                const px1 = timeToPx(conn.t1); const px2 = timeToPx(conn.t2);
                const py1 = state.flatTracks[tIdx1].centerY + state.topMargin; 
                const py2 = state.flatTracks[tIdx2].centerY + state.topMargin;
                let cpx = px1 + (px2 - px1) / 2; let cpy = (tIdx1 === tIdx2) ? py1 - 60 : py1;
                let bestT = 0.5; let minDist = Infinity;
                for (let i = 0; i <= 50; i++) {
                    let t = i / 50; let invT = 1 - t;
                    let curX = invT * invT * px1 + 2 * invT * t * cpx + t * t * px2;
                    let curY = invT * invT * py1 + 2 * invT * t * cpy + t * t * py2;
                    let dist = (mx - curX)**2 + (my - curY)**2;
                    if (dist < minDist) { minDist = dist; bestT = t; }
                }
                conn.textPos = Math.max(0.08, Math.min(0.92, bestT)); render();
            }
        }
        return;
    }

    if (state.mode === 'TEXT' && isDraggingText && state.selectedTextId) {
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if (t) {
            const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
            if (track) {
                t.t = pxToTime(mx - dragOffset.x);
                t.y = my - (track.centerY + state.topMargin) - dragOffset.y; 
                render();
            }
        }
        return;
    }

    let oldHover = state.hoverEdgeT;
    if (state.subMode === 'REPEAT_START' || state.subMode === 'REPEAT_END' || state.measureMode !== 'IDLE' || state.arrowMode !== 'IDLE') {
        const hoverT = pxToTime(mx);
        let closestEdgeT = null; let minDistancePx = Infinity;
        
        const hitTrackIdx = getTrackIdxAtY(my - state.topMargin);
        if (hitTrackIdx >= 0 && hitTrackIdx < state.flatTracks.length) {
            const hitTrack = state.flatTracks[hitTrackIdx];
            if (hitTrack.node.type !== 'group' && hitTrack.node.data) {
                hitTrack.node.data.forEach(ev => {
                    const distPx = Math.abs(timeToPx(hoverT) - timeToPx(ev.t));
                    if (distPx < minDistancePx) { minDistancePx = distPx; closestEdgeT = ev.t; }
                });
            }
        }
        state.hoverEdgeT = minDistancePx <= 15 ? closestEdgeT : null;
    } else {
        state.hoverEdgeT = null;
    }
    
    if (oldHover !== state.hoverEdgeT) { render(); }
});

window.addEventListener('mouseup', () => { 
    state.dragArrowConnId = null; 
    isDraggingText = false; 
    render();
});

waveContainer.addEventListener('mousedown', (e) => {
    if (document.activeElement.tagName === 'INPUT' && document.activeElement.id !== 'busValueInput') return;
    const rect = waveContainer.getBoundingClientRect();
    const mx = e.clientX - rect.left + state.offsetX;
    const my = e.clientY - rect.top + state.offsetY; 
    const clickedT = pxToTime(mx);

    if (state.mode === 'TEXT') {
        let hit = null;
        for (let i = state.texts.length - 1; i >= 0; i--) {
            const t = state.texts[i];
            const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
            if(!track) continue; 
            const tX = timeToPx(t.t); 
            const tY_Absolute = track.centerY + t.renderY + state.topMargin; 

            if (t.zoomLevel === 1 && t.isSticky && mx >= tX && mx <= tX + 20 && my <= tY_Absolute && my >= tY_Absolute - t.size) {
                t.collapsed = !t.collapsed; 
                t.baseTimeWidth = undefined; 
                render(); 
                return; 
            }
            if (mx >= tX && mx <= tX + t.currentFullWidth && my <= tY_Absolute + (t.isSticky && !t.collapsed ? t.renderedHeight - t.size : 0) && my >= tY_Absolute - t.size) { 
                hit = t; break; 
            }
        }
        
        if (hit) {
            state.selectedTextId = hit.id; 
            isDraggingText = true; 
            const hitTrack = state.flatTracks.find(tr => tr.node.id === hit.trackId);
            dragOffset = { x: mx - timeToPx(hit.t), y: my - (hitTrack.centerY + hit.renderY + state.topMargin) };
        } else {
            state.selectedTextId = null;
            const bTrack = state.flatTracks.find(tr => tr.node.id === state.boundTrackId);
            if(bTrack) {
                let relY = Math.max(20, my - (bTrack.centerY + state.topMargin)); 
                startTextEdit(e.clientX - rect.left, e.clientY - rect.top, relY, bTrack.node.id);
            }
        }
        render(); return;
    }

    const hitTrackIdx = getTrackIdxAtY(my - state.topMargin);
    const hitTrack = state.flatTracks[hitTrackIdx];
    
    if (state.arrowMode !== 'IDLE' || state.measureMode !== 'IDLE') {
        if (!hitTrack) return;
        if (state.hoverEdgeT === null) return; 
        const snappedT = state.hoverEdgeT;
        
        if (state.measureMode === 'MEASURE_P1') {
            state.tempMeasurePoint = { t: snappedT, sigId: hitTrack.node.id }; state.measureMode = 'MEASURE_P2';
        } else if (state.measureMode === 'MEASURE_P2') {
            if (snappedT !== state.tempMeasurePoint.t) {
                state.measurements.push({ id: 'm_'+Date.now(), t1: state.tempMeasurePoint.t, sigId1: state.tempMeasurePoint.sigId, t2: snappedT, sigId2: hitTrack.node.id, text: 'Δt', color: '#f1c40f', thickness: 1, arrowType: 'two-way' });
            }
            state.measureMode = 'IDLE'; state.tempMeasurePoint = null; document.getElementById('btnMeasure').classList.remove('active');
        } else if (state.arrowMode === 'ARROW_P1') {
            state.tempArrowPoint = { t: snappedT, sigId: hitTrack.node.id }; state.arrowMode = 'ARROW_P2';
        } else if (state.arrowMode === 'ARROW_P2') {
            if (snappedT !== state.tempArrowPoint.t || hitTrack.node.id !== state.tempArrowPoint.sigId) {
                state.connections.push({ id: 'conn_'+Date.now(), t1: state.tempArrowPoint.t, sigId1: state.tempArrowPoint.sigId, t2: snappedT, sigId2: hitTrack.node.id, text: 'Event', color: '#e74c3c', thickness: 2 });
            }
            state.arrowMode = 'IDLE'; state.tempArrowPoint = null; document.getElementById('btnArrow').classList.remove('active');
        }
        updateUI(); return;
    }

    let hitArrowTextConn = null;
    for (let conn of state.connections) {
        if (!conn.text) continue;
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === conn.sigId1); const tIdx2 = state.flatTracks.findIndex(t => t.node.id === conn.sigId2);
        if (tIdx1 === -1 || tIdx2 === -1) continue;
        const px1 = timeToPx(conn.t1); const px2 = timeToPx(conn.t2);
        const py1 = state.flatTracks[tIdx1].centerY + state.topMargin; const py2 = state.flatTracks[tIdx2].centerY + state.topMargin;
        let cpx = px1 + (px2 - px1) / 2; let cpy = (tIdx1 === tIdx2) ? py1 - 60 : py1;
        const tParam = conn.textPos !== undefined ? conn.textPos : 0.5; const invT = 1 - tParam;
        const textX = invT * invT * px1 + 2 * invT * tParam * cpx + tParam * tParam * px2;
        const textY = invT * invT * py1 + 2 * invT * tParam * cpy + tParam * tParam * py2;
        if (Math.abs(mx - textX) <= 20 && Math.abs(my - textY) <= 10) { hitArrowTextConn = conn; break; }
    }

    if (hitArrowTextConn) {
        state.dragArrowConnId = hitArrowTextConn.id; state.selectedConnId = hitArrowTextConn.id; state.selectedMeasureId = null;
        updateUI(); return; 
    }

    let hitMeasure = null;
    for (let m of state.measurements) {
        if (m.absoluteRenderY === undefined) continue; 
        const absPx1 = timeToPx(m.t1); const absPx2 = timeToPx(m.t2);
        const absCenterX = (absPx1 + absPx2) / 2;
        if (mx >= Math.min(absPx1, absCenterX-30)-10 && mx <= Math.max(absPx1, absCenterX+30)+10 && Math.abs(my - (m.absoluteRenderY + state.topMargin)) < 15) { hitMeasure = m; break; }
    }
    
    let hitConn = null;
    for (let conn of state.connections) {
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === conn.sigId1); const tIdx2 = state.flatTracks.findIndex(t => t.node.id === conn.sigId2);
        if (tIdx1 === -1 || tIdx2 === -1) continue;
        const px1 = timeToPx(conn.t1); const px2 = timeToPx(conn.t2);
        const py1 = state.flatTracks[tIdx1].centerY + state.topMargin; const py2 = state.flatTracks[tIdx2].centerY + state.topMargin;
        let cpx = px1 + (px2 - px1) / 2; let cpy = (tIdx1 === tIdx2) ? py1 - 60 : py1;
        const steps = 10; let minDistance = Infinity;
        for (let i = 0; i <= steps; i++) {
            const t = i / steps; const invT = 1 - t;
            const curX = invT * invT * px1 + 2 * invT * t * cpx + t * t * px2;
            const curY = invT * invT * py1 + 2 * invT * t * cpy + t * t * py2;
            minDistance = Math.min(minDistance, Math.sqrt((mx - curX) ** 2 + (my - curY) ** 2));
        }
        if (minDistance <= 10) { hitConn = conn; break; }
    }

    if (hitConn) { 
        state.selectedConnId = hitConn.id; state.selectedMeasureId = null; 
    } else if (hitMeasure) { 
        state.selectedMeasureId = hitMeasure.id; state.selectedConnId = null; 
    } else {
        state.selectedConnId = null;
        state.selectedMeasureId = null;
    }

    if (hitTrackIdx >= 0 && hitTrackIdx < state.flatTracks.length) {
        if (state.mode === 'VIEW') {
            if(!e.ctrlKey) state.selectedIds.clear();
            state.selectedIds.add(hitTrack.node.id);
        }
    }
    const sigs = getSelectedSignals();

    if ((state.mode === 'INSERT' || state.mode === 'EDIT') && sigs.length > 0) {
        if (state.subMode === 'REPEAT_START' && state.hoverEdgeT !== null) {
            state.repeatStartT = state.hoverEdgeT; state.subMode = 'REPEAT_END'; state.hoverEdgeT = null;
        } else if (state.subMode === 'REPEAT_END' && state.hoverEdgeT !== null && state.hoverEdgeT > state.repeatStartT) {
            state.repeatEndT = state.hoverEdgeT; state.subMode = 'REPEAT_MODAL'; 
            repeatModal.style.display = 'flex'; repeatInput.value = lastRepeatValue;
            setTimeout(() => { repeatInput.focus(); repeatInput.select(); }, 10);
        } else if ((state.subMode === 'NORMAL' || state.subMode === 'VALUE') && state.pendingVal) {
            if (state.mode === 'INSERT' && clickedT > state.cursorT) {
                const dur = clickedT - state.cursorT;
                sigs.forEach(sig => applyDrawAction(sig, state.cursorT, dur, state.pendingVal));
                state.cursorT += dur; togglePendingVal(sigs);
                if (state.subMode === 'VALUE') { state.subMode = 'NORMAL'; busValueInput.blur(); }
            }
        }
    } 
    
    if ((state.mode === 'VIEW' || ((state.mode === 'EDIT' || state.mode === 'INSERT') && (state.subMode === 'NORMAL' || state.subMode === 'VALUE'))) && sigs.length > 0) {
        let closestEdge = null; let minDistancePx = Infinity;
        sigs[0].data.forEach(event => {
            const distPx = Math.abs(timeToPx(clickedT) - timeToPx(event.t));
            if (distPx < minDistancePx) { minDistancePx = distPx; closestEdge = event; }
        });
        if (closestEdge && minDistancePx <= 10) state.cursorT = closestEdge.t;
    }
    updateUI();
});

function startTextEdit(screenX, screenY, relY, trackId) {
    textInputOverlay.style.display = 'block';
    textInputOverlay.style.left = `${screenX}px`; textInputOverlay.style.top = `${screenY - 14}px`; 
    textInputOverlay.value = ''; textInputOverlay.dataset.t = pxToTime(screenX + state.offsetX);
    textInputOverlay.dataset.relY = relY; textInputOverlay.dataset.trackId = trackId;
    setTimeout(() => { textInputOverlay.focus(); }, 10);
}

textInputOverlay.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
        const val = textInputOverlay.value.trim();
        if (val) {
            state.texts.push({ id: 'txt_' + Date.now(), text: val, t: parseFloat(textInputOverlay.dataset.t), y: parseFloat(textInputOverlay.dataset.relY), trackId: textInputOverlay.dataset.trackId, size: 16, baseScale: state.scaleX, color: '#f1c40f', bgColor: '#2d2d30', isSticky: false, content: '', collapsed: true });
        }
        textInputOverlay.style.display = 'none'; waveContainer.focus(); updateUI();
    } else if (e.key === 'Escape') { textInputOverlay.style.display = 'none'; waveContainer.focus(); render(); }
});

function getVisibleTracks() {
    return state.flatTracks;
}

window.addEventListener('keydown', (e) => {
    if (document.activeElement.tagName === 'INPUT' || document.activeElement.tagName === 'TEXTAREA') return; 
    const k = e.key.toLowerCase(); const sigs = getSelectedSignals();

    if (k === 't' && state.mode !== 'TEXT') { e.preventDefault(); state.mode = 'TEXT'; state.boundTrackId = sigs.length > 0 ? sigs[0].id : (state.flatTracks[0] ? state.flatTracks[0].node.id : null); updateUI(); return; }
    if (k === 'm') { e.preventDefault(); toggleMeasureMode(); return; }
    if (k === 'a') { e.preventDefault(); toggleArrowMode(); return; }

    if (k === 'c') { 
        if (state.mode === 'TEXT' && state.selectedTextId) { e.preventDefault(); openAttrModal(); return; }
        
        let selectedGroups = Array.from(state.selectedIds).map(id => findNodeAndParent(state.tree, id)?.node).filter(n => n?.type === 'group');
        
        if (state.selectedMeasureId || state.selectedConnId || sigs.length > 0 || selectedGroups.length > 0) { 
            e.preventDefault(); openAttrModal(); return; 
        }
    }

    if (e.key === 'Delete') {
        if (state.mode === 'TEXT' && state.selectedTextId) { state.texts = state.texts.filter(t => t.id !== state.selectedTextId); state.selectedTextId = null; updateUI(); return; }
        if (state.selectedMeasureId) { state.measurements = state.measurements.filter(m => m.id !== state.selectedMeasureId); state.selectedMeasureId = null; updateUI(); return; }
        if (state.selectedConnId) { state.connections = state.connections.filter(c => c.id !== state.selectedConnId); state.selectedConnId = null; updateUI(); return; }
        if (state.selectedIds.size > 0) {
            state.selectedIds.forEach(id => { let info = findNodeAndParent(state.tree, id); if (info) info.list.splice(info.index, 1); });
            state.selectedIds.clear(); updateUI(); return;
        }
    }

    if (e.ctrlKey && k === 'g') {
        e.preventDefault();
        if (state.selectedIds.size > 0) {
            let newGroup = { id: 'g_' + Date.now(), type: 'group', name: 'New Group', expanded: true, children: [] };
            let firstInfo = null; let nodesToGroup = [];
            state.selectedIds.forEach(id => {
                let info = findNodeAndParent(state.tree, id);
                if (info) { if (!firstInfo) firstInfo = info; nodesToGroup.push(info.node); info.list.splice(info.index, 1); }
            });
            newGroup.children = nodesToGroup;
            if (firstInfo) firstInfo.list.splice(firstInfo.index, 0, newGroup); else state.tree.push(newGroup);
            state.selectedIds.clear(); state.selectedIds.add(newGroup.id); updateUI();
        }
        return;
    }

    if (k === 'i' && state.mode === 'VIEW' && sigs.length > 0) { e.preventDefault(); state.mode = 'INSERT'; state.pendingVal = sigs[0].type==='single'?'1':'z'; state.subMode = 'NORMAL'; updateUI(); return; }
    if (k === 'e' && state.mode === 'VIEW' && sigs.length > 0) { e.preventDefault(); state.mode = 'EDIT'; state.pendingVal = sigs[0].type==='single'?'1':'z'; state.subMode = 'NORMAL'; updateUI(); return; }
    if (e.key === 'Escape') {
        if (state.subMode !== 'NORMAL') { state.subMode = 'NORMAL'; updateUI(); return; }
        if (state.mode !== 'VIEW') { state.mode = 'VIEW'; state.pendingVal = null; busValueInput.blur(); updateUI(); return; }
    }

    if (state.mode === 'VIEW') {
        let visible = getVisibleTracks();
        let idx = visible.findIndex(t => state.selectedIds.has(t.node.id));
        let changed = false;
        if (e.key === 'ArrowDown') { e.preventDefault(); idx = Math.min(visible.length - 1, idx + 1); changed = true; }
        if (e.key === 'ArrowUp') { e.preventDefault(); idx = Math.max(0, idx - 1); changed = true; }
        if (changed && idx >= 0 && idx < visible.length) { 
            state.selectedIds.clear(); state.selectedIds.add(visible[idx].node.id); updateUI(); 
        }
    }

    if (e.key === 'ArrowLeft' || e.key === 'ArrowRight') {
        if (sigs.length > 0 && (state.subMode === 'NORMAL' || state.subMode === 'VALUE')) {
            const edges = getEdges(sigs[0], state.cursorT);
            if (e.key === 'ArrowLeft') state.cursorT = edges.prev;
            if (e.key === 'ArrowRight') state.cursorT = edges.next !== Infinity ? edges.next : state.cursorT + 10;
            const pxX = timeToPx(state.cursorT); const rect = waveContainer.getBoundingClientRect();
            if(pxX < state.offsetX || pxX > state.offsetX + rect.width) { state.offsetX = Math.max(0, pxX - rect.width/2); }
            updateUI();
        }
    }

    if ((state.mode === 'INSERT' || state.mode === 'EDIT') && sigs.length > 0) {
        const mainSig = sigs[0];
        if (k === 'r' && state.subMode === 'NORMAL') { e.preventDefault(); state.subMode = 'REPEAT_START'; state.hoverEdgeT = null; updateUI(); return; }
        if (state.subMode !== 'NORMAL') return;

        if (mainSig.type === 'single' && ['0', '1', 'x', 'z'].includes(k)) { state.pendingVal = k; return; }
        if (mainSig.type === 'multi') {
            if (k === 'x' || k === 'z') { state.pendingVal = k; updateUI(); return; }
            if (k === 'v') { e.preventDefault(); state.subMode = 'VALUE'; updateUI(); return; }
        }

        if (e.key === 'Enter' && state.pendingVal) {
            if (state.mode === 'INSERT') {
                durationModal.style.display = 'flex'; durationInput.value = lastDurationValue;
                setTimeout(() => { durationInput.focus(); durationInput.select(); }, 10);
            } else if (state.mode === 'EDIT') {
                sigs.forEach(sig => editCurrentSegment(sig, state.cursorT, state.pendingVal));
                togglePendingVal(sigs); updateUI();
            }
            return;
        }

        if (e.key === ' ' && state.pendingVal) {
            e.preventDefault();
            if (state.mode === 'INSERT') {
                let dur = parseFloat(lastDurationValue) || 10;
                const snapInfo = findNodeAndParent(state.tree, state.snapTargetId);
                if (snapInfo && snapInfo.node.type !== 'group') {
                    const edges = getEdges(snapInfo.node, state.cursorT);
                    if (edges.next !== Infinity) dur = edges.next - state.cursorT;
                }
                sigs.forEach(sig => applyDrawAction(sig, state.cursorT, dur, state.pendingVal));
                state.cursorT += dur;
            }
        }

        if (e.key === 'Backspace') {
            const edges = getEdges(mainSig, state.cursorT);
            if (edges.prev < state.cursorT) { sigs.forEach(sig => deleteAndPull(sig, edges.prev, state.cursorT)); state.cursorT = edges.prev; }
        }
    }
});

busValueInput.addEventListener('keydown', (e) => {
    state.pendingVal = e.target.value.trim() || 'z';
    const sigs = getSelectedSignals();

    if (e.key === ' ') {
        e.preventDefault(); e.stopPropagation();
        if (state.mode === 'INSERT') {
            let dur = parseFloat(lastDurationValue) || 10;
            const snapInfo = findNodeAndParent(state.tree, state.snapTargetId);
            if (sigs.length > 0 && state.pendingVal) {
                if (snapInfo && snapInfo.node.type !== 'group') {
                    const edges = getEdges(snapInfo.node, state.cursorT);
                    if (edges.next !== Infinity) dur = edges.next - state.cursorT;
                }
                sigs.forEach(sig => applyDrawAction(sig, state.cursorT, dur, state.pendingVal));
                state.cursorT += dur; state.subMode = 'NORMAL'; updateUI(); waveContainer.focus();
            }
        }
    } else if (e.key === 'Enter') {
        e.preventDefault(); e.stopPropagation();
        if (state.mode === 'INSERT') {
            durationModal.style.display = 'flex'; durationInput.value = lastDurationValue;
            setTimeout(() => { durationInput.focus(); durationInput.select(); }, 10);
        } else if (state.mode === 'EDIT') {
            if (sigs.length > 0 && state.pendingVal) {
                sigs.forEach(sig => editCurrentSegment(sig, state.cursorT, state.pendingVal));
                togglePendingVal(sigs); state.subMode = 'NORMAL'; updateUI(); waveContainer.focus();
            }
        }
    } else if (e.key === 'Escape') { state.subMode = 'NORMAL'; busValueInput.blur(); updateUI(); waveContainer.focus(); }
});
busValueInput.addEventListener('input', (e) => { state.pendingVal = e.target.value.trim() || 'z'; });

waveContainer.addEventListener('wheel', (e) => {
    e.preventDefault();
    if (state.mode === 'TEXT' && state.selectedTextId && !e.ctrlKey && !e.shiftKey) {
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if (t) {
            t.size = Math.max(10, Math.min(100, t.size + (e.deltaY > 0 ? -2 : 2)));
            t.baseScale = state.scaleX; t.baseTimeWidth = undefined; updateUI(); return;
        }
    }

    if (e.ctrlKey) {
        const zoomDelta = e.deltaY > 0 ? 0.8 : 1.25;
        const mouseX = e.clientX - waveContainer.getBoundingClientRect().left;
        const absoluteT = pxToTime(mouseX + state.offsetX);
        state.scaleX = Math.max(1, Math.min(state.scaleX * zoomDelta, 400));
        state.offsetX = Math.max(0, timeToPx(absoluteT) - mouseX);
    } else { state.offsetX = Math.max(0, state.offsetX + e.deltaY); }
    updateUI();
});

function closeModal(id) { 
    document.getElementById(id).style.display = 'none'; 
    if (id === 'repeatModal') state.subMode = 'NORMAL'; 
    if(id === 'attrModal') state.addingSignalType = null; 
    waveContainer.focus(); 
    updateUI(); 
}

function confirmDuration() {
    const raw = durationInput.value.trim().toLowerCase(); const match = raw.match(/^([\d.]+)\s*(ns|us|ms)?$/);
    if (match) {
        lastDurationValue = durationInput.value.trim(); let val = parseFloat(match[1]); let unit = match[2] || 'ns';
        if (unit === 'us') val *= 1000; if (unit === 'ms') val *= 1000000;
        const sigs = getSelectedSignals();
        if (sigs.length > 0 && state.pendingVal && val > 0 && state.mode === 'INSERT') {
            sigs.forEach(sig => applyDrawAction(sig, state.cursorT, val, state.pendingVal));
            state.cursorT += val; togglePendingVal(sigs); 
            if (state.subMode === 'VALUE') state.subMode = 'NORMAL';
        }
    }
    closeModal('durationModal');
}

function confirmRepeat() {
    let count = parseInt(repeatInput.value.trim(), 10);
    if (!isNaN(count) && count > 0) {
        lastRepeatValue = count.toString(); const sigs = getSelectedSignals();
        if (sigs.length > 0) {
            if (state.mode === 'INSERT') {
                sigs.forEach(sig => insertPatternAndPush(sig, state.cursorT, state.repeatStartT, state.repeatEndT, count));
                state.cursorT = state.cursorT + (state.repeatEndT - state.repeatStartT) * count;
            } else if (state.mode === 'EDIT') { sigs.forEach(sig => overwritePatternAndStay(sig, state.cursorT, state.repeatStartT, state.repeatEndT, count)); }
        }
    }
    closeModal('repeatModal');
}

function openAttrModal() {
    const thickRow = document.getElementById('thicknessRow'); 
    const arrowTypeRow = document.getElementById('arrowTypeRow');
    const stickyRow = document.getElementById('stickyRow'); 
    const contentRow = document.getElementById('contentRow');
    const bgColorRow = document.getElementById('bgColorRow'); 
    const radixRow = document.getElementById('radixRow');
    const colorRow = document.getElementById('colorRow'); // 获取Color配置行
    
    // 初始化隐藏所有高级选项
    if (stickyRow) stickyRow.style.display = 'none'; 
    if (contentRow) contentRow.style.display = 'none';
    if (bgColorRow) bgColorRow.style.display = 'none'; 
    if (arrowTypeRow) arrowTypeRow.style.display = 'none';
    if (radixRow) radixRow.style.display = 'none'; 
    if (thickRow) thickRow.style.display = 'none';
    if (colorRow) colorRow.style.display = 'flex'; // 默认显示颜色选项

    document.getElementById('attrModal').style.display = 'flex';
    
    let selectedGroups = Array.from(state.selectedIds).map(id => findNodeAndParent(state.tree, id)?.node).filter(n => n?.type === 'group');

    // 1. 如果处于【添加新信号】状态
    if (state.addingSignalType) {
        document.getElementById('modalTitle').innerText = 'Add New Signal';
        document.getElementById('modalName').value = state.addingSignalType === 'multi' ? 'bus_new' : 'sig_new';
        document.getElementById('modalColor').value = state.addingSignalType === 'multi' ? '#9b59b6' : '#2ecc71';
        if (thickRow) { thickRow.style.display = 'flex'; document.getElementById('modalThickness').value = 2; }
        if (state.addingSignalType === 'multi') { radixRow.style.display = 'flex'; document.getElementById('modalRadix').value = 'hex'; }
    }
    // 2. 如果正在编辑标尺
    else if (state.selectedMeasureId) {
        document.getElementById('modalTitle').innerText = 'Measure Properties'; 
        const m = state.measurements.find(x => x.id === state.selectedMeasureId);
        document.getElementById('modalName').value = m.text || ''; 
        document.getElementById('modalColor').value = m.color;
        if (thickRow) { thickRow.style.display = 'flex'; document.getElementById('modalThickness').value = m.thickness; }
        if (arrowTypeRow) { arrowTypeRow.style.display = 'flex'; document.getElementById('modalArrowType').value = m.arrowType || 'two-way'; }
    } 
    // 3. 如果正在编辑事件连线
    else if (state.selectedConnId) {
        document.getElementById('modalTitle').innerText = 'Arrow Connection Properties'; 
        const c = state.connections.find(x => x.id === state.selectedConnId);
        document.getElementById('modalName').value = c.text || ''; 
        document.getElementById('modalColor').value = c.color;
        if (thickRow) { thickRow.style.display = 'flex'; document.getElementById('modalThickness').value = c.thickness; }
    }
    // 4. 如果正在编辑文本/便签
    else if (state.mode === 'TEXT' && state.selectedTextId) {
        document.getElementById('modalTitle').innerText = 'Text / Note Properties'; 
        const t = state.texts.find(x => x.id === state.selectedTextId);
        document.getElementById('modalName').value = t.text || ''; 
        document.getElementById('modalColor').value = t.color;
        if (bgColorRow) { bgColorRow.style.display = 'flex'; document.getElementById('modalBgColor').value = t.bgColor || '#2d2d30'; }
        if (stickyRow) stickyRow.style.display = 'flex'; 
        if (contentRow) contentRow.style.display = 'flex';
        document.getElementById('modalIsSticky').checked = !!t.isSticky; 
        document.getElementById('modalTextContent').value = t.content || '';
    } 
    // 5. 如果正在编辑 Group 组名
    else if (selectedGroups.length > 0) {
        document.getElementById('modalTitle').innerText = 'Group Properties'; 
        const grp = selectedGroups[0];
        document.getElementById('modalName').value = grp.name; 
        if (colorRow) colorRow.style.display = 'none'; // 分组不需要调整颜色
    }
    // 6. 默认：编辑当前选中的已有信号
    else {
        const sigs = getSelectedSignals(); 
        // 只有在这里（非添加模式下）没选中信号才关闭面板
        if (sigs.length === 0) { closeModal('attrModal'); return; }
        
        document.getElementById('modalTitle').innerText = 'Signal Properties'; 
        const sig = sigs[0];
        document.getElementById('modalName').value = sig.name; 
        document.getElementById('modalColor').value = sig.color;
        if (thickRow) { thickRow.style.display = 'flex'; document.getElementById('modalThickness').value = sig.thickness || 2; }
        if (sig.type === 'multi') { radixRow.style.display = 'flex'; document.getElementById('modalRadix').value = sig.radix || 'hex'; }
    }
    
    // 自动聚焦输入框
    setTimeout(() => { document.getElementById('modalName').focus(); document.getElementById('modalName').select(); }, 10);
}

function applyAttrModal() {
    if (state.addingSignalType) {
        const newSig = { id: 's_' + Date.now(), type: state.addingSignalType, name: document.getElementById('modalName').value.trim() || 'new_sig', color: document.getElementById('modalColor').value, thickness: parseInt(document.getElementById('modalThickness').value) || 2, data: [{t:0, val:'z'}] };
        if(state.addingSignalType === 'multi') newSig.radix = document.getElementById('modalRadix').value || 'hex';
        state.tree.push(newSig); state.selectedIds.clear(); state.selectedIds.add(newSig.id); 
        state.addingSignalType = null; updateUI(); closeModal('attrModal'); return;
    }

    if (state.selectedMeasureId) {
        const m = state.measurements.find(x => x.id === state.selectedMeasureId);
        if (m) { m.text = document.getElementById('modalName').value.trim(); m.color = document.getElementById('modalColor').value; m.thickness = parseInt(document.getElementById('modalThickness').value) || 1; m.arrowType = document.getElementById('modalArrowType').value; }
    } 
    else if (state.selectedConnId) {
        const c = state.connections.find(x => x.id === state.selectedConnId);
        if (c) { c.text = document.getElementById('modalName').value.trim(); c.color = document.getElementById('modalColor').value; c.thickness = parseInt(document.getElementById('modalThickness').value) || 1; }
    }
    else if (state.mode === 'TEXT' && state.selectedTextId) {
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if(t) {
            t.text = document.getElementById('modalName').value.trim(); t.color = document.getElementById('modalColor').value; t.bgColor = document.getElementById('modalBgColor').value;
            t.isSticky = document.getElementById('modalIsSticky').checked; t.content = document.getElementById('modalTextContent').value;
            t.baseScale = state.scaleX; t.baseTimeWidth = undefined; 
        }
    }
    else {
        let selectedGroups = Array.from(state.selectedIds).map(id => findNodeAndParent(state.tree, id)?.node).filter(n => n?.type === 'group');
        if (selectedGroups.length > 0) {
            selectedGroups.forEach(grp => {
                grp.name = document.getElementById('modalName').value.trim() || grp.name;
            });
        } else {
            const sigs = getSelectedSignals();
            sigs.forEach(sig => {
                sig.name = document.getElementById('modalName').value.trim() || sig.name; 
                sig.color = document.getElementById('modalColor').value; 
                sig.thickness = parseInt(document.getElementById('modalThickness').value) || 2;
                if (sig.type === 'multi') sig.radix = document.getElementById('modalRadix').value;
            });
        }
    }
    updateUI(); closeModal('attrModal');
}

['durationInput', 'repeatInput', 'modalName', 'modalThickness', 'scaleInput'].forEach(id => {
    const el = document.getElementById(id);
    if(el) {
        el.addEventListener('keydown', (e) => {
            e.stopPropagation(); 
            if (e.key === 'Enter') { 
                if (id === 'durationInput') confirmDuration(); 
                else if (id === 'repeatInput') confirmRepeat(); 
                else if (id === 'scaleInput') applyScaleModal();
                else applyAttrModal(); 
            }
            if (e.key === 'Escape') closeModal(e.target.closest('.modal').id);
        });
    }
});

// ==========================================
// 导出与导入功能 (JSON)
// ==========================================
function exportWaveform() {
    const exportData = {
        tree: state.tree,
        texts: state.texts,
        measurements: state.measurements,
        connections: state.connections,
        scaleX: state.scaleX
    };
    const dataStr = JSON.stringify(exportData, null, 2);
    const blob = new Blob([dataStr], { type: "application/json" });
    const url = URL.createObjectURL(blob); 
    const a = document.createElement('a'); 
    a.href = url; 
    a.download = `digi_wave_export.json`; 
    document.body.appendChild(a); 
    a.click(); 
    URL.revokeObjectURL(url);
}

function importWaveform() {
    document.getElementById('fileInput').click();
}

function handleFileImport(event) {
    const file = event.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = function(e) {
        try {
            const importedData = JSON.parse(e.target.result);
            state.tree = importedData.tree || [];
            state.texts = importedData.texts || [];
            state.measurements = importedData.measurements || [];
            state.connections = importedData.connections || [];
            state.scaleX = importedData.scaleX || 10;
            
            // 重置视图状态
            state.selectedIds.clear();
            state.selectedTextId = null;
            state.selectedMeasureId = null;
            state.selectedConnId = null;
            state.offsetX = 0; state.offsetY = 0;
            
            updateUI();
        } catch (err) {
            alert("读取失败：文件损坏或格式不正确！\n" + err.message);
        }
        event.target.value = '';
    };
    reader.readAsText(file);
}

function loadDefaultWaveform() {
    fetch('digiwave_default.json')
        .then(response => {
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
            return response.json();
        })
        .then(importedData => {
            state.tree = importedData.tree || [];
            state.texts = importedData.texts || [];
            state.measurements = importedData.measurements || [];
            state.connections = importedData.connections || [];
            state.scaleX = importedData.scaleX || 10;
            updateUI();
        })
        .catch(e => {
            console.log("Could not load default digiwave_default.json. Initializing as empty.", e.message);
            // 确保如果加载失败是全空
            state.tree = [];
            state.texts = [];
            state.measurements = [];
            state.connections = [];
            updateUI(); 
        });
}

function addSignal(type) {
    state.addingSignalType = type;
    openAttrModal();
}

resizeCanvas(); 
loadDefaultWaveform(); // 启动时加载默认波形
requestAnimationFrame(loop);