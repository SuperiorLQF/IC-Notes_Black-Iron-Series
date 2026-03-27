let state = {
    cycles: 100,
    scaleX: 50,
    offsetX: 0,
    offsetY: 0,
    topMargin: 40, 
    
    cursorX: 0, 
    cursorY: 0, 
    
    mode: 'wave', 
    boundTrackId: null, 

    printMode: false, 
    cmdType: '',  
    isModalOpen: false, 
    isEditingText: false,
    
    gaps: new Set(), 
    GAP_WIDTH: 24,   
    
    texts: [], 
    selectedTextId: null, 
    
    selectedIds: new Set(),

    measurements: [], 
    selectedMeasureId: null,
    measureMode: 'IDLE', 
    tempMeasurePoint: null,

    // 【新增】智能填充相关状态
    fill: { hovered: null, dragging: false, currentC: -1, lastHoveredId: null },

    totalTracksHeight: 0, 

    tree: [
        { id: 'c1', name: 'clk', type: 'clock', color: '#ffffff', data: [] },
        { id: 'g1', name: 'AXI Read Channel', type: 'group', color: '#555555', expanded: true, children: [
            { id: 'm1', name: 'araddr', type: 'multi', color: '#3498db', radix: 'hex', data: ['0x00', '0x1A', '0x1A', '"Addr"'] },
            { id: 's1', name: 'arvalid', type: 'single', color: '#e74c3c', data: ['0','1','x','z'] }
        ]},
        { id: 'm2', name: 'rdata', type: 'multi', color: '#f1c40f', radix: 'dec', data: ['10', '255', 'x', 'z'] }
    ],
    
    flatTracks: []
};

const canvas = document.getElementById('waveCanvas');
const ctx = canvas.getContext('2d');
const waveContainer = document.getElementById('waveContainer');
const busInput = document.getElementById('busInput');
const attrModal = document.getElementById('attrModal');
const helpModal = document.getElementById('helpModal');
const textInputOverlay = document.getElementById('textInputOverlay');
const modeToggle = document.getElementById('modeToggle');
const printToggle = document.getElementById('printToggle');
const btnMeasure = document.getElementById('btnMeasure');

let lastKey = '';
let lastKeyTime = 0;

function rebuildFlatTracks() {
    let result = [];
    function flatten(nodes, depth, parentArray) {
        for (let i = 0; i < nodes.length; i++) {
            const node = nodes[i];
            result.push({ node, depth, parentArray, index: i });
            if (node.type === 'group' && node.expanded && node.children) {
                flatten(node.children, depth + 1, node.children);
            }
        }
    }
    flatten(state.tree, 0, state.tree);
    state.flatTracks = result;
    if (state.flatTracks.length === 0) {
        state.cursorY = 0;
    } else {
        state.cursorY = Math.max(0, Math.min(state.flatTracks.length - 1, state.cursorY));
    }
}

function findNodeInfo(nodes, id, parentArray = null) {
    for (let i = 0; i < nodes.length; i++) {
        if (nodes[i].id === id) return { node: nodes[i], array: nodes, index: i, parentArray };
        if (nodes[i].type === 'group') {
            const res = findNodeInfo(nodes[i].children, id, nodes[i].children);
            if (res) return res;
        }
    }
    return null;
}

function refreshAll() { rebuildFlatTracks(); renderSignalList(); render(); }

const m2Info = findNodeInfo(state.tree, 'm2');
for(let i=10; i<15; i++) m2Info.node.data[i] = '0xFF';
rebuildFlatTracks();

function toggleMeasureMode() {
    state.measureMode = state.measureMode === 'IDLE' ? 'MEASURE_P1' : 'IDLE';
    state.tempMeasurePoint = null;
    if (state.measureMode !== 'IDLE') btnMeasure.classList.add('active');
    else btnMeasure.classList.remove('active');
    render();
}

function toggleGroup(id, e) {
    if(e) e.stopPropagation();
    const info = findNodeInfo(state.tree, id);
    if (info) { info.node.expanded = !info.node.expanded; refreshAll(); }
}

function ungroup(groupId, e) {
    if(e) e.stopPropagation();
    const info = findNodeInfo(state.tree, groupId);
    if (!info) return;
    const groupNode = info.node;
    info.array.splice(info.index, 1, ...(groupNode.children || []));
    if(state.selectedIds.has(groupId)) state.selectedIds.delete(groupId);
    refreshAll();
}

function groupSelected() {
    if (state.selectedIds.size < 1) return;
    const firstTrack = state.flatTracks.find(t => state.selectedIds.has(t.node.id));
    if (!firstTrack) return;
    const insertTarget = findNodeInfo(state.tree, firstTrack.node.id);

    const extracted = [];
    function extract(nodes) {
        for (let i = 0; i < nodes.length; i++) {
            if (state.selectedIds.has(nodes[i].id)) {
                extracted.push(nodes.splice(i, 1)[0]); i--; 
            } else if (nodes[i].type === 'group') { extract(nodes[i].children); }
        }
    }
    extract(state.tree);

    const newGroup = { id: 'g_' + Date.now(), type: 'group', name: 'New Group', expanded: true, color: '#555555', children: extracted };
    const safeIdx = Math.min(insertTarget.index, insertTarget.array.length);
    insertTarget.array.splice(safeIdx, 0, newGroup);

    state.selectedIds.clear(); state.selectedIds.add(newGroup.id);
    refreshAll();
}

function deleteSelectedSignal() {
    if (state.flatTracks.length === 0) return;
    const sigId = state.flatTracks[state.cursorY].node.id;
    const info = findNodeInfo(state.tree, sigId);
    if (info) {
        info.array.splice(info.index, 1);
        if (state.selectedIds.has(sigId)) state.selectedIds.delete(sigId);
        refreshAll();
    }
}

function getTheme() {
    if (state.printMode) {
        return {
            bg: '#ffffff', grid: '#dddddd', text: '#000000',
            cursorBg: 'rgba(0,0,0,0.05)', cursorLine: '#000000',
            xState: '#666666', zState: '#aaaaaa', gapBg: '#ffffff', gapLine: '#555555',
            measureBase: '#000000', tempMeasure: '#333333', getSigColor: (c) => '#000000' 
        };
    } else {
        return {
            bg: '#000000', grid: '#333333', text: '#666666',
            cursorBg: 'rgba(52, 152, 219, 0.3)', cursorLine: '#3498db',
            xState: '#e74c3c', zState: '#7f8c8d', gapBg: '#080808', gapLine: '#555555',
            measureBase: null, tempMeasure: '#ffff00', getSigColor: (c) => c
        };
    }
}

function togglePrintMode() {
    state.printMode = !state.printMode;
    if (state.printMode) {
        document.body.classList.add('print-theme'); printToggle.classList.add('active'); printToggle.innerText = 'PRINT: ON';
    } else {
        document.body.classList.remove('print-theme'); printToggle.classList.remove('active'); printToggle.innerText = 'PRINT: OFF';
    }
    renderSignalList(); render();
}

function resizeCanvas() {
    const rect = waveContainer.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    canvas.width = rect.width * dpr; canvas.height = rect.height * dpr;
    canvas.style.width = `${rect.width}px`; canvas.style.height = `${rect.height}px`;
    ctx.scale(dpr, dpr); render();
}
window.addEventListener('resize', resizeCanvas);

function toggleMode(targetMode) {
    state.mode = targetMode || (state.mode === 'wave' ? 'text' : 'wave');
    if (state.mode === 'text') {
        const boundId = Array.from(state.selectedIds)[0] || (state.flatTracks[0] ? state.flatTracks[0].node.id : null);
        state.boundTrackId = boundId;
        const boundNode = findNodeInfo(state.tree, boundId)?.node;
        modeToggle.innerText = `LAYER: TEXT [Bound: ${boundNode ? boundNode.name : 'None'}]`;
        modeToggle.className = 'mode-btn text-mode';
        waveContainer.style.cursor = 'default';
    } else {
        state.boundTrackId = null;
        modeToggle.innerText = 'LAYER: WAVE';
        modeToggle.className = 'mode-btn';
        waveContainer.style.cursor = 'crosshair';
        state.selectedTextId = null;
    }
    render();
}

function buildCycleMap() {
    let cycleX = [];
    let currentX = 0;
    for (let i = 0; i <= state.cycles; i++) {
        if (state.gaps.has(i)) currentX += state.GAP_WIDTH;
        cycleX.push(currentX);
        currentX += state.scaleX;
    }
    return cycleX;
}

function cycleToPx(cFloat) {
    const intC = Math.floor(cFloat);
    const frac = cFloat - intC;
    const cycleX = buildCycleMap();
    if (intC >= state.cycles) return cycleX[state.cycles];
    if (intC < 0) return 0;
    return cycleX[intC] + frac * state.scaleX;
}

function pxToCycle(px) {
    const cycleX = buildCycleMap();
    for (let i = 0; i < state.cycles; i++) {
        const cxStart = cycleX[i];
        const cxEnd = cxStart + state.scaleX;
        const hitBoxStart = state.gaps.has(i) ? cxStart - state.GAP_WIDTH : cxStart;
        if (px >= hitBoxStart && px < cxEnd) {
            if (px < cxStart) return i; 
            return i + (px - cxStart) / state.scaleX;
        }
    }
    return state.cycles;
}

function getTrackIdxAtY(yPx) {
    for (let i = 0; i < state.flatTracks.length; i++) {
        let t = state.flatTracks[i];
        if (yPx >= t.yOffset && yPx < t.yOffset + t.height) return i;
    }
    return Math.max(0, state.flatTracks.length - 1);
}

function ensureCursorVisible() {
    if(state.mode !== 'wave') return;
    const rect = waveContainer.getBoundingClientRect();
    const cycleX = buildCycleMap();
    
    const curPxX = cycleX[state.cursorX];
    if (curPxX < state.offsetX) state.offsetX = curPxX;
    if (curPxX + state.scaleX > state.offsetX + rect.width) state.offsetX = curPxX + state.scaleX - rect.width;

    const track = state.flatTracks[state.cursorY];
    if (!track) return;
    const curPxY = track.yOffset;
    if (curPxY < state.offsetY) state.offsetY = curPxY;
    if (curPxY + track.height > state.offsetY + rect.height - state.topMargin) {
        state.offsetY = curPxY + track.height - rect.height + state.topMargin;
    }
    
    const maxScrollY = Math.max(0, state.totalTracksHeight + state.topMargin - rect.height);
    state.offsetY = Math.min(state.offsetY, maxScrollY); 
    
    render();
}

function renderSignalList() {
    const signalListEl = document.getElementById('signalList');
    signalListEl.innerHTML = '';
    
    state.flatTracks.forEach((track, idx) => {
        const sig = track.node;
        const row = document.createElement('div');
        
        row.style.height = track.height + 'px';
        row.style.transform = `translateY(${-state.offsetY}px)`;
        row.style.paddingLeft = `${10 + track.depth * 15}px`;
        
        row.draggable = true;
        row.ondragstart = (e) => { e.dataTransfer.setData('text/plain', sig.id); };
        row.ondragover = (e) => { 
            e.preventDefault(); 
            const rect = row.getBoundingClientRect();
            const y = e.clientY - rect.top;
            if (y < rect.height / 2) {
                row.classList.add('drag-over-top'); row.classList.remove('drag-over-bottom');
            } else {
                row.classList.add('drag-over-bottom'); row.classList.remove('drag-over-top');
            }
        };
        row.ondragleave = (e) => { row.classList.remove('drag-over-top', 'drag-over-bottom'); };
        row.ondrop = (e) => {
            const isTopHalf = row.classList.contains('drag-over-top');
            row.classList.remove('drag-over-top', 'drag-over-bottom');
            const sourceId = e.dataTransfer.getData('text/plain');
            if (sourceId === sig.id) return;
            
            const sourceInfo = findNodeInfo(state.tree, sourceId);
            const targetInfo = findNodeInfo(state.tree, sig.id);
            if (!sourceInfo || !targetInfo) return;

            let isDescendant = false;
            function check(n) { if (n.id === sig.id) isDescendant = true; if (n.type==='group') n.children.forEach(check); }
            check(sourceInfo.node);
            if (isDescendant) return;

            const srcNode = sourceInfo.node;
            sourceInfo.array.splice(sourceInfo.index, 1);
            
            const newTargetInfo = findNodeInfo(state.tree, sig.id);
            if (!newTargetInfo) { refreshAll(); return; }
            
            let insertIdx = newTargetInfo.index;
            if (!isTopHalf) insertIdx++; 
            
            newTargetInfo.array.splice(insertIdx, 0, srcNode);
            refreshAll();
        };

        row.onclick = (e) => {
            if (state.mode === 'wave') {
                if (e.ctrlKey) {
                    if (state.selectedIds.has(sig.id)) state.selectedIds.delete(sig.id);
                    else state.selectedIds.add(sig.id);
                } else {
                    state.selectedIds.clear(); state.selectedIds.add(sig.id);
                }
                state.cursorY = idx; waveContainer.focus(); ensureCursorVisible();
            }
        };

        let innerHTML = '';
        if (sig.type === 'group') {
            innerHTML += `<div class="group-toggle" onclick="toggleGroup('${sig.id}', event)">${sig.expanded ? '▼' : '▶'}</div>`;
        } else {
            innerHTML += `<div style="width:16px; margin-right:4px;"></div>`; 
        }

        const boxColor = state.printMode ? '#000' : sig.color;
        let radixLabel = sig.type === 'multi' ? `<span style="opacity:0.6; font-size:11px; margin-left:5px;">[${sig.radix}]</span>` : '';
        
        innerHTML += `<div style="width:12px; height:12px; background:${boxColor}; border-radius:2px; margin-right:5px; flex-shrink:0;"></div>`;
        innerHTML += `<span class="signal-name" title="${sig.name}">${sig.name}${radixLabel}</span>`;
        if (sig.type === 'group') {
            innerHTML += `<button class="ungroup-btn" onclick="ungroup('${sig.id}', event)">Ungroup</button>`;
        }
        row.innerHTML = innerHTML;
        signalListEl.appendChild(row);
    });
    
    const sigName = state.flatTracks[state.cursorY]?.node.name || '';
    document.getElementById('statusCursor').innerText = `Track: ${sigName} | Cycle: ${state.cursorX}`;
}

function addSignal(type) {
    const name = prompt("Signal Name:", type === 'clock' ? 'clk_new' : 'sig_new');
    if (!name) return;
    const colors = { 'clock': '#ffffff', 'single': '#2ecc71', 'multi': '#9b59b6' };
    
    const newSig = { id: 's_'+Date.now(), name: name, type: type, color: colors[type], radix: 'hex', data: [] };
    state.tree.push(newSig);
    state.selectedIds.clear(); state.selectedIds.add(newSig.id);
    refreshAll();
    state.cursorY = state.flatTracks.length - 1;
    ensureCursorVisible();
}

function parseDisplayStr(val, sig) {
    if (!val) return { str: 'z', isX: false, isZ: true };
    const lower = val.toLowerCase();
    if (lower === 'z') return { str: 'z', isX: false, isZ: true };
    if (lower === 'x') return { str: 'x', isX: true, isZ: false };
    if (val.startsWith('"') && val.endsWith('"')) return { str: val.substring(1, val.length - 1), isX:false, isZ:false };
    
    let numVal = NaN;
    if (lower.startsWith('0x')) numVal = parseInt(val, 16);
    else if (/^-?\d+$/.test(val)) numVal = parseInt(val, 10);
    
    if (!isNaN(numVal)) {
        if (sig.radix === 'hex') return { str: '0x' + numVal.toString(16).toUpperCase(), isX:false, isZ:false };
        if (sig.radix === 'dec') return { str: numVal.toString(10), isX:false, isZ:false };
    }
    return { str: val, isX: false, isZ: false };
}

// 【新增】提取指定周期所在的 Multi 信号"格子"的起止范围
function getMultiBlockAtCycle(sig, cycle) {
    if (cycle < 0 || cycle >= state.cycles) return null;
    const val = sig.data[cycle] || 'z';
    if (['z', 'x'].includes(val.toLowerCase())) return null; // z 和 x 不作为智能拖拽起点
    
    let start = cycle;
    while (start > 0 && (sig.data[start - 1] || 'z') === val && !state.gaps.has(start)) start--;
    let end = cycle;
    while (end + 1 < state.cycles && (sig.data[end + 1] || 'z') === val && !state.gaps.has(end + 1)) end++;
    
    return { start, end, val };
}

// 【新增】智能递增函数
function incrementValue(valStr, step, radix) {
    if (!valStr) return valStr;
    const lower = valStr.toLowerCase();
    if (valStr.startsWith('"') && valStr.endsWith('"')) return valStr; // 字符串原样复制
    
    let numVal = NaN;
    if (lower.startsWith('0x')) numVal = parseInt(valStr, 16);
    else if (/^-?\d+$/.test(valStr)) numVal = parseInt(valStr, 10);

    if (!isNaN(numVal)) {
        let nextNum = numVal + step;
        if (lower.startsWith('0x') || radix === 'hex') {
            return '0x' + nextNum.toString(16).toUpperCase();
        } else {
            return nextNum.toString(10);
        }
    }
    return valStr; // 无法解析的也原样复制
}

function computeTrackLayout() {
    state.flatTracks.forEach(t => {
        t.topSpace = 0;
        t.bottomSpace = 0;
        t.height = 40; 
    });

    // ==========================================
    // 1. 标尺布局 (强制在上方)
    // ==========================================
    let trackIntervals = {};
    let activeMeasurements = [];
    state.measurements.forEach(m => m.absoluteRenderY = undefined);
    state.measurements.forEach(m => {
        const tIdx1 = state.flatTracks.findIndex(t => t.node.id === m.sigId1);
        const tIdx2 = state.flatTracks.findIndex(t => t.node.id === m.sigId2);
        if (tIdx1 === -1 || tIdx2 === -1) return; 
        
        m._currentTIdx1 = tIdx1;
        m._currentTIdx2 = tIdx2;
        activeMeasurements.push(m);
    });
    
    activeMeasurements.forEach(m => {
        const minTrackIdx = Math.min(m._currentTIdx1, m._currentTIdx2);
        if (!trackIntervals[minTrackIdx]) trackIntervals[minTrackIdx] = [];
        
        const absX1 = cycleToPx(m.c1);
        const absX2 = cycleToPx(m.c2);
        const pxWidth = Math.abs(absX2 - absX1);

        let textW = 0;
        if (pxWidth >= 35) {
            ctx.font = (state.selectedMeasureId === m.id ? "bold " : "") + `14px Consolas, sans-serif`;
            textW = ctx.measureText(m.text || 'Δt').width;
            textW = Math.min(textW, pxWidth - 4); 
        } else if (pxWidth >= 10) {
            textW = 6;
        }

        trackIntervals[minTrackIdx].push({ 
            m, 
            min: Math.min(absX1, absX2) - textW/2 - 5, 
            max: Math.max(absX1, absX2) + textW/2 + 5 
        });
    });

    for (let tIdx in trackIntervals) {
        let placed = [];
        let maxL = 0;
        trackIntervals[tIdx].sort((a,b) => a.min - b.min);
        trackIntervals[tIdx].forEach(inv => {
            let lane = 0;
            let collision = true;
            while(collision) {
                collision = false;
                for(let p of placed) {
                    if (p.lane === lane && inv.min < p.max && inv.max > p.min) {
                        collision = true; break;
                    }
                }
                if (!collision) break;
                lane++;
            }
            placed.push({ ...inv, lane });
            inv.m.assignedLane = lane; 
            maxL = Math.max(maxL, lane);
        });
        let topNeed = 42 + maxL * 20; 
        state.flatTracks[tIdx].topSpace = Math.max(state.flatTracks[tIdx].topSpace, topNeed - 20);
    }

    // ==========================================
    // 2. 文本布局 (无形物理容器 + 完美跟随波形比例 + 透明降级防跳动)
    // ==========================================
    let textsByTrack = {};
    state.texts.forEach(t => {
        if (!t.trackId) return;
        if (!textsByTrack[t.trackId]) textsByTrack[t.trackId] = [];
        textsByTrack[t.trackId].push(t);
        
        ctx.font = `${t.size}px Consolas, sans-serif`;
        
        // 【已修复】加上基础边距避免初期截断
        let rawW = ctx.measureText(t.text || 'Note').width + (t.isSticky ? 28 : 8);
        let totalH = t.size;
        
        if (t.isSticky) {
            let lines = t.collapsed ? [] : (t.content || '').split('\n');
            if (!t.collapsed) {
                ctx.font = `${t.size * 0.85}px Consolas, sans-serif`;
                lines.forEach(l => { rawW = Math.max(rawW, ctx.measureText(l).width + 12); });
                totalH = t.size + 12 + (lines.length * t.size * 0.9);
                ctx.font = `${t.size}px Consolas, sans-serif`;
            } else {
                totalH = t.size + 4;
            }
        }
        
        t.renderedHeight = totalH;

        if (!t.baseCycleWidth) {
            t.baseScale = t.baseScale || state.scaleX;
            t.baseCycleWidth = rawW / t.baseScale;
        }

        let strictPxWidth = t.baseCycleWidth * state.scaleX;
        t.currentFullWidth = strictPxWidth;

        if (strictPxWidth < 6) {
            t.zoomLevel = 3;     
        } else if (strictPxWidth < 25) {
            t.zoomLevel = 2;     
        } else {
            t.zoomLevel = 1;     
        }
    });

    for (let trkId in textsByTrack) {
        const track = state.flatTracks.find(tr => tr.node.id === trkId);
        if (!track) continue;

        let tList = textsByTrack[trkId];
        tList.sort((a, b) => a.y - b.y);

        let placedBelow = [];
        const WAVE_BOT = 18; 

        tList.forEach(t => {
            let currentY = Math.max(t.y, WAVE_BOT + t.size); 
            let topEdge = currentY - t.size - 4;
            
            if (topEdge < WAVE_BOT) currentY += (WAVE_BOT - topEdge);
            
            let collision = true;
            let safety = 0;
            while (collision && safety < 50) {
                collision = false;
                for (let p of placedBelow) {
                    let tMinX = cycleToPx(t.cycle);
                    let tMaxX = tMinX + t.currentFullWidth;
                    let pMinX = cycleToPx(p.cycle);
                    let pMaxX = pMinX + p.currentFullWidth;
                    
                    if (tMinX < pMaxX + 5 && tMaxX + 5 > pMinX) {
                        let tTop = currentY - t.size - 4;
                        let pBot = p.renderY - p.size + p.renderedHeight + 4;
                        if (tTop < pBot) {
                            currentY += (pBot - tTop); 
                            collision = true; break;
                        }
                    }
                }
                safety++;
            }
            t.renderY = currentY;
            placedBelow.push(t);
        });

        placedBelow.forEach(t => {
            let bottomEdge = t.renderY - t.size + t.renderedHeight + 4;
            if (bottomEdge > 20) track.bottomSpace = Math.max(track.bottomSpace, bottomEdge - 20);
        });
    }

    let currentY = 0;
    state.flatTracks.forEach(t => {
        t.height = 40 + t.topSpace + t.bottomSpace;
        t.yOffset = currentY;
        t.centerY = currentY + 20 + t.topSpace; 
        currentY += t.height;
    });
    state.totalTracksHeight = currentY; 
}

function render() {
    const rect = waveContainer.getBoundingClientRect();
    const width = rect.width;
    const height = rect.height;
    const theme = getTheme();

    computeTrackLayout();
    
    const signalRows = document.getElementById('signalList').children;
    state.flatTracks.forEach((track, idx) => {
        if (signalRows[idx]) {
            signalRows[idx].style.height = track.height + 'px';
            signalRows[idx].style.transform = `translateY(${-state.offsetY}px)`;
            
            let isSelected = false;
            let isActive = false;
            let isTextBound = false;

            if (state.mode === 'wave') {
                isSelected = state.selectedIds.has(track.node.id);
                isActive = (idx === state.cursorY);
            } else if (state.mode === 'text') {
                isTextBound = (state.boundTrackId === track.node.id);
            }
            
            signalRows[idx].className = `signal-row ${isSelected ? 'selected' : ''} ${isActive ? 'active' : ''} ${isTextBound ? 'text-bound' : ''}`;
        }
    });
    
    ctx.fillStyle = theme.bg;
    ctx.fillRect(0, 0, width, height);
    
    const cycleX = buildCycleMap();

    ctx.setLineDash([2, 2]); ctx.lineWidth = 1; ctx.strokeStyle = theme.grid;
    ctx.beginPath();
    for (let i = 0; i <= state.cycles; i++) {
        const x = cycleX[i] - state.offsetX;
        if (x >= 0 && x <= width) { ctx.moveTo(x, 0); ctx.lineTo(x, height); }
    }
    ctx.stroke(); ctx.setLineDash([]); 

    state.flatTracks.forEach((track, idx) => {
        const absTop = track.yOffset - state.offsetY + state.topMargin;
        if (state.mode === 'text' && state.boundTrackId === track.node.id) {
            ctx.fillStyle = state.printMode ? 'rgba(0,0,0,0.05)' : 'rgba(155, 89, 182, 0.25)';
            ctx.fillRect(0, absTop, width, track.height);
        } 
        else if (state.mode === 'wave' && state.selectedIds.has(track.node.id)) {
            ctx.fillStyle = state.printMode ? 'rgba(0,0,0,0.03)' : 'rgba(52, 152, 219, 0.15)';
            ctx.fillRect(0, absTop, width, track.height);
        }
    });

    if (state.mode === 'wave') {
        if (state.flatTracks[state.cursorY]) {
            const t = state.flatTracks[state.cursorY];
            const activeY = t.yOffset - state.offsetY + state.topMargin;
            ctx.fillStyle = theme.cursorBg;
            ctx.fillRect(0, activeY, width, t.height); 

            if (t.node.type !== 'group') {
                const cursorPxX = cycleX[state.cursorX] - state.offsetX;
                const coreActiveY = t.centerY - 20 - state.offsetY + state.topMargin; 
                const coreHeight = 40; 

                ctx.fillRect(cursorPxX, coreActiveY, state.scaleX, coreHeight);
                ctx.strokeStyle = theme.cursorLine; ctx.lineWidth = 1;
                ctx.strokeRect(cursorPxX, coreActiveY, state.scaleX, coreHeight);
            }
        }
    }

    ctx.save();
    state.gaps.forEach(g => {
        const rightX = cycleX[g] - state.offsetX;
        const leftX = rightX - state.GAP_WIDTH;
        if (rightX < 0 || leftX > width) return;

        ctx.fillStyle = theme.gapBg;
        ctx.fillRect(leftX, 0, state.GAP_WIDTH, height);

        ctx.strokeStyle = theme.gapLine;
        ctx.lineWidth = 1; ctx.setLineDash([4, 4]); 
        ctx.beginPath();
        ctx.moveTo(leftX + 4, 0); ctx.lineTo(leftX + 4, height);
        ctx.moveTo(rightX - 4, 0); ctx.lineTo(rightX - 4, height);
        ctx.stroke();
        ctx.setLineDash([]);
    });
    ctx.restore();

    state.flatTracks.forEach((track, idx) => {
        const sig = track.node;
        const absTop = track.yOffset - state.offsetY + state.topMargin;
        if (absTop > height || absTop + track.height < 0) return;

        if (sig.type === 'group') {
            ctx.fillStyle = state.printMode ? '#f9f9f9' : '#1a1a1c';
            ctx.fillRect(0, absTop + 2, width, track.height - 4);
            return;
        }

        const yMid = track.centerY - state.offsetY + state.topMargin;
        const yHigh = yMid - 12; 
        const yLow = yMid + 12;  
        const drawColor = theme.getSigColor(sig.color);

        ctx.strokeStyle = drawColor; ctx.fillStyle = drawColor; ctx.lineWidth = 2;
        
        if (sig.type === 'clock') {
            ctx.beginPath();
            for (let i = 0; i < state.cycles; i++) {
                const startX = cycleX[i] - state.offsetX;
                const endX = startX + state.scaleX;
                const midX = startX + state.scaleX / 2;
                if (i === 0 || state.gaps.has(i)) ctx.moveTo(startX, yLow);
                else ctx.lineTo(startX, yLow);
                ctx.lineTo(startX, yHigh); ctx.lineTo(midX, yHigh);
                ctx.lineTo(midX, yLow); ctx.lineTo(endX, yLow);
            }
            ctx.stroke();
        }
        else if (sig.type === 'single') {
            ctx.beginPath();
            let lastVal = null;
            for (let i = 0; i < state.cycles; i++) {
                const startX = cycleX[i] - state.offsetX;
                const endX = startX + state.scaleX;
                const val = sig.data[i] || 'z';
                let y = yMid;
                if (val === '1') y = yHigh; else if (val === '0') y = yLow;

                if (i === 0 || state.gaps.has(i)) ctx.moveTo(startX, y); 
                else if (val !== lastVal) ctx.lineTo(startX, y);

                if (val.toLowerCase() === 'x') {
                    ctx.stroke(); ctx.beginPath(); ctx.strokeStyle = theme.xState; 
                    ctx.moveTo(startX, y); ctx.lineTo(endX, y);
                    ctx.stroke(); ctx.beginPath(); ctx.strokeStyle = drawColor; 
                } else if (val.toLowerCase() === 'z') {
                    ctx.stroke(); ctx.beginPath(); ctx.strokeStyle = theme.zState; 
                    ctx.moveTo(startX, y); ctx.lineTo(endX, y);
                    ctx.stroke(); ctx.beginPath(); ctx.strokeStyle = drawColor;
                } else { ctx.lineTo(endX, y); }
                lastVal = val;
            }
            ctx.stroke();
        }
        else if (sig.type === 'multi') {
            let startIdx = 0;
            while (startIdx < state.cycles) {
                const val = sig.data[startIdx] || 'z';
                let endIdx = startIdx;
                while (endIdx + 1 < state.cycles && (sig.data[endIdx + 1] || 'z') === val && !state.gaps.has(endIdx + 1)) {
                    endIdx++;
                }
                
                const xStart = cycleX[startIdx] - state.offsetX;
                const xEnd = cycleX[endIdx] + state.scaleX - state.offsetX;
                const boxWidth = xEnd - xStart;
                const boxHeight = yLow - yHigh; 
                
                if (xEnd > 0 && xStart < width) {
                    const parsed = parseDisplayStr(val, sig);
                    
                    if (parsed.isZ) {
                        ctx.beginPath(); ctx.strokeStyle = theme.zState;
                        ctx.moveTo(xStart, yMid); ctx.lineTo(xEnd, yMid); ctx.stroke();
                        ctx.strokeStyle = drawColor;
                    } 
                    else if (parsed.isX) {
                        ctx.beginPath(); ctx.strokeStyle = theme.xState;
                        ctx.strokeRect(xStart, yHigh, boxWidth, boxHeight);
                        ctx.save(); ctx.beginPath(); ctx.rect(xStart, yHigh, boxWidth, boxHeight); ctx.clip(); 
                        ctx.beginPath(); ctx.strokeStyle = theme.xState; ctx.lineWidth = 1;
                        for (let x = xStart - boxHeight; x < xEnd; x += 6) {
                            ctx.moveTo(x, yLow); ctx.lineTo(x + boxHeight, yHigh);
                        }
                        ctx.stroke(); ctx.restore();
                        ctx.strokeStyle = drawColor; ctx.fillStyle = drawColor;
                    } 
                    else {
                        ctx.beginPath(); ctx.strokeRect(xStart, yHigh, boxWidth, boxHeight);
                        ctx.font = '12px Consolas, sans-serif'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
                        const maxTextW = boxWidth - 4;
                        if (maxTextW > 10) {
                            if (ctx.measureText(parsed.str).width > maxTextW) {
                                let str = parsed.str;
                                if(boxWidth < 20) ctx.fillText('...', xStart + boxWidth/2, yMid);
                                else {
                                    while(str.length > 0 && ctx.measureText(str+'...').width > maxTextW) str = str.slice(0,-1);
                                    ctx.fillText(str+'...', xStart + boxWidth/2, yMid);
                                }
                            }
                            else ctx.fillText(parsed.str, xStart + boxWidth/2, yMid);
                        }
                    }
                }
                startIdx = endIdx + 1;
            }
        }
    });

    if (state.measureMode === 'MEASURE_P2' && state.tempMeasurePoint) {
        const px = cycleToPx(state.tempMeasurePoint.c) - state.offsetX;
        ctx.strokeStyle = theme.tempMeasure; 
        ctx.lineWidth = 1; ctx.setLineDash([5, 5]);
        ctx.beginPath(); ctx.moveTo(px, 0); ctx.lineTo(px, height); ctx.stroke();
        ctx.setLineDash([]);
    }

    // ==========================================
    // 渲染标尺 
    // ==========================================
    state.measurements.forEach(m => {
        if (m._currentTIdx1 === undefined || m._currentTIdx2 === undefined) return;
        const track1 = state.flatTracks[m._currentTIdx1];
        const track2 = state.flatTracks[m._currentTIdx2];
        const minTrack = m._currentTIdx1 < m._currentTIdx2 ? track1 : track2;
        
        const px1 = cycleToPx(m.c1) - state.offsetX;
        const px2 = cycleToPx(m.c2) - state.offsetX;
        const pxWidth = Math.abs(px2 - px1);
        
        if (pxWidth < 3) return;

        m.absoluteRenderY = minTrack.centerY - 26 - (m.assignedLane * 20);
        const py1 = track1.centerY - state.offsetY + state.topMargin;
        const py2 = track2.centerY - state.offsetY + state.topMargin;
        const isSelected = (state.selectedMeasureId === m.id);

        const drawColor = theme.measureBase || m.color; 
        ctx.strokeStyle = drawColor;
        ctx.fillStyle = drawColor;
        ctx.lineWidth = isSelected ? m.thickness + 1 : m.thickness;

        if (isSelected && !state.printMode) {
            ctx.shadowColor = drawColor; ctx.shadowBlur = 8;
        } else {
            ctx.shadowBlur = 0; 
        }

        const midY = m.absoluteRenderY - state.offsetY + state.topMargin; 

        if (pxWidth >= 20) {
            ctx.setLineDash([4, 4]);
            ctx.beginPath();
            ctx.moveTo(px1, py1); ctx.lineTo(px1, midY);
            ctx.moveTo(px2, py2); ctx.lineTo(px2, midY);
            ctx.stroke();
        }

        ctx.setLineDash([]);
        ctx.beginPath();
        ctx.moveTo(px1, midY); ctx.lineTo(px2, midY);
        ctx.stroke();

        if (pxWidth >= 25) {
            const head = Math.min(10, pxWidth / 3);
            ctx.beginPath();
            const dir1 = px1 < px2 ? 1 : -1;
            ctx.moveTo(px1, midY); ctx.lineTo(px1 + dir1*head, midY - 3);
            ctx.moveTo(px1, midY); ctx.lineTo(px1 + dir1*head, midY + 3);
            const dir2 = px2 < px1 ? 1 : -1;
            ctx.moveTo(px2, midY); ctx.lineTo(px2 + dir2*head, midY - 3);
            ctx.moveTo(px2, midY); ctx.lineTo(px2 + dir2*head, midY + 3);
            ctx.stroke();
        }

        if (pxWidth >= 35) {
            ctx.font = (isSelected ? "bold " : "") + `14px Consolas, sans-serif`;
            ctx.textAlign = "center";
            ctx.textBaseline = "bottom";
            let dtText = m.text || 'Δt';
            let maxW = pxWidth - 4;
            if (ctx.measureText(dtText).width > maxW) {
                while (dtText.length > 0 && ctx.measureText(dtText + '...').width > maxW) {
                    dtText = dtText.slice(0, -1);
                }
                dtText += '...';
            }
            ctx.fillText(dtText, (px1 + px2) / 2, midY - 2);
        } else if (pxWidth >= 10) {
            ctx.fillRect((px1+px2)/2 - 3, midY - 3, 6, 6);
        }
        ctx.shadowBlur = 0; 
    });

    // ==========================================
    // 渲染文本 (绝对容器，框体限制)
    // ==========================================
    state.texts.forEach(t => {
        const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
        if (!track) return; 

        const screenX = cycleToPx(t.cycle) - state.offsetX;
        const screenY = track.centerY + t.renderY - state.offsetY + state.topMargin;
        const boxPx = t.currentFullWidth; 
        
        const dSize = t.size;             
        const totalH = t.renderedHeight;  

        if (state.mode === 'text' && state.selectedTextId === t.id) {
            ctx.strokeStyle = theme.cursorLine; ctx.lineWidth = 1; ctx.setLineDash([4, 4]);
            ctx.strokeRect(screenX - 2, screenY - dSize - 6, boxPx + 4, totalH + 8);
            ctx.setLineDash([]);
        }

        if (t.zoomLevel === 3) return; 

        if (t.zoomLevel === 2) {
            if (t.isSticky) {
                ctx.fillStyle = state.printMode ? '#ffffff' : (t.bgColor || '#2d2d30');
                ctx.strokeStyle = state.printMode ? '#000000' : (t.color || '#f1c40f');
                ctx.fillRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);
                ctx.strokeRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);
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
            ctx.strokeStyle = state.printMode ? '#000000' : (t.color || '#f1c40f');
            ctx.lineWidth = 1;
            ctx.fillRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);
            ctx.strokeRect(screenX, screenY - dSize - 4, boxPx, totalH + 4);

            if (boxPx >= 20) {
                ctx.fillStyle = state.printMode ? '#000000' : (t.color || '#f1c40f');
                ctx.beginPath();
                if (t.collapsed) {
                    ctx.moveTo(screenX + 6, screenY - dSize/2 - 4);
                    ctx.lineTo(screenX + 6, screenY - dSize/2 + 4);
                    ctx.lineTo(screenX + 12, screenY - dSize/2);
                } else {
                    ctx.moveTo(screenX + 4, screenY - dSize/2 - 2);
                    ctx.lineTo(screenX + 14, screenY - dSize/2 - 2);
                    ctx.lineTo(screenX + 9, screenY - dSize/2 + 4);
                }
                ctx.fill();
            }

            ctx.font = `${dSize}px Consolas, sans-serif`;
            let titleStr = displayStr;
            let availableTitleW = boxPx - 20; 
            if (availableTitleW > 0) {
                if (ctx.measureText(titleStr).width > availableTitleW) {
                    while (titleStr.length > 0 && ctx.measureText(titleStr + '...').width > availableTitleW) {
                        titleStr = titleStr.slice(0, -1);
                    }
                    if (titleStr.length > 0 || availableTitleW > 15) titleStr += '...';
                }
                ctx.fillStyle = state.printMode ? '#000000' : (t.color || '#f1c40f');
                ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
                ctx.fillText(titleStr, screenX + 18, screenY);
            }

            if (!t.collapsed) {
                ctx.fillStyle = state.printMode ? '#333333' : theme.text;
                ctx.font = `${dSize * 0.85}px Consolas, sans-serif`;
                lines.forEach((l, i) => {
                    let lineStr = l;
                    let availableLineW = boxPx - 10;
                    if (availableLineW > 0) {
                        if (ctx.measureText(lineStr).width > availableLineW) {
                            while (lineStr.length > 0 && ctx.measureText(lineStr + '...').width > availableLineW) {
                                lineStr = lineStr.slice(0, -1);
                            }
                            if (lineStr.length > 0) lineStr += '...';
                        }
                        ctx.fillText(lineStr, screenX + 6, screenY + dSize + (i * dSize * 0.9));
                    }
                });
            }
        } else {
            ctx.font = `${dSize}px Consolas, sans-serif`;
            ctx.fillStyle = state.printMode ? '#000000' : t.color;
            ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
            
            let availableW = boxPx - 4; 
            if (availableW > 0) {
                if (ctx.measureText(displayStr).width > availableW) {
                    while (displayStr.length > 0 && ctx.measureText(displayStr + '...').width > availableW) {
                        displayStr = displayStr.slice(0, -1);
                    }
                    displayStr += '...';
                }
                ctx.fillText(displayStr, screenX, screenY);
            }
        }
    });

    // ==========================================
    // 【新增】渲染智能填充手柄 (Excel Style) 和 拖拽预览框
    // ==========================================
    if (state.mode === 'wave' && state.fill && (state.fill.hovered || state.fill.dragging)) {
        const h = state.fill.hovered;
        const track = state.flatTracks[h.tIdx];
        if (track) {
            const endPx = cycleX[h.end] + state.scaleX - state.offsetX;
            const yMid = track.centerY - state.offsetY + state.topMargin;
            const yLow = yMid + 12;
            const yHigh = yMid - 12;

            // 黑色小方块（加个小白边防暗色背景糊在一起）
            ctx.fillStyle = '#000000';
            ctx.fillRect(endPx - 4, yLow - 4, 8, 8);
            ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 1;
            ctx.strokeRect(endPx - 4, yLow - 4, 8, 8);

            // 拖拽时的绿色预览框
            if (state.fill.dragging && state.fill.currentC > h.end) {
                const startPx = cycleX[h.end + 1] - state.offsetX;
                const previewEndPx = cycleX[state.fill.currentC] + state.scaleX - state.offsetX;
                
                ctx.strokeStyle = '#2ecc71'; // Excel 绿
                ctx.lineWidth = 2;
                ctx.setLineDash([4, 4]);
                ctx.strokeRect(startPx, yHigh, previewEndPx - startPx, yLow - yHigh);
                ctx.setLineDash([]);
            }
        }
    }

    document.getElementById('statusZoom').innerText = `Scale: ${Math.round(state.scaleX)} px/cycle`;
}

let isDraggingText = false;
let dragOffset = { x: 0, y: 0 };

waveContainer.addEventListener('mousedown', (e) => {
    if (state.isModalOpen || state.cmdType) return;
    waveContainer.focus();
    const rect = waveContainer.getBoundingClientRect();
    
    // 【新增】拦截智能填充柄的按下事件
    if (state.fill.hovered) {
        state.fill.dragging = true;
        state.fill.currentC = state.fill.hovered.end;
        return;
    }

    const mx = e.clientX - rect.left + state.offsetX;
    const my = e.clientY - rect.top + state.offsetY - state.topMargin; 

    if (state.measureMode !== 'IDLE') {
        const snappedC = Math.round(pxToCycle(mx)); 
        const hitTrackIdx = getTrackIdxAtY(my); 
        
        if (hitTrackIdx < 0 || hitTrackIdx >= state.flatTracks.length) return;
        const hitTrack = state.flatTracks[hitTrackIdx];
        if (!hitTrack) return; 
        const hitSigId = hitTrack.node.id;
        
        if (state.measureMode === 'MEASURE_P1') {
            state.tempMeasurePoint = { c: snappedC, sigId: hitSigId }; 
            state.measureMode = 'MEASURE_P2';
            btnMeasure.classList.add('active'); 
        } else if (state.measureMode === 'MEASURE_P2') {
            if (snappedC !== state.tempMeasurePoint.c) {
                const newM = {
                    id: 'm_' + Date.now(),
                    c1: state.tempMeasurePoint.c, sigId1: state.tempMeasurePoint.sigId, 
                    c2: snappedC, sigId2: hitSigId, 
                    text: 'Δt',
                    color: '#00FF00', 
                    thickness: 1,
                    baseScale: state.scaleX
                };
                state.measurements.push(newM);
            }
            state.measureMode = 'IDLE';
            state.tempMeasurePoint = null;
            btnMeasure.classList.remove('active');
        }
        render();
        return;
    }

    if (state.mode === 'wave') {
        state.cursorX = Math.floor(pxToCycle(mx));
        state.cursorX = Math.max(0, Math.min(state.cycles - 1, state.cursorX));
        state.cursorY = getTrackIdxAtY(my);

        const hitTrack = state.flatTracks[state.cursorY];
        if (hitTrack && hitTrack.node.type !== 'group') {
            if (!e.ctrlKey) {
                state.selectedIds.clear();
            }
            state.selectedIds.add(hitTrack.node.id);
        }

        let hitMeasure = null;
        for (let m of state.measurements) {
            if (m.absoluteRenderY === undefined) continue; 
            const absPx1 = cycleToPx(m.c1);
            const absPx2 = cycleToPx(m.c2);
            const absMinX = Math.min(absPx1, absPx2);
            const absMaxX = Math.max(absPx1, absPx2);
            const absCenterX = (absPx1 + absPx2) / 2;
            
            const absHitMinX = Math.min(absMinX, absCenterX - 30);
            const absHitMaxX = Math.max(absMaxX, absCenterX + 30);

            if (mx >= absHitMinX - 10 && mx <= absHitMaxX + 10 && Math.abs(my - m.absoluteRenderY) < 15) {
                hitMeasure = m; break;
            }
        }
        if (hitMeasure) {
            state.selectedMeasureId = hitMeasure.id;
        } else {
            state.selectedMeasureId = null; 
        }
        ensureCursorVisible();
        return;
    }

    if (state.mode === 'text') {
        let hit = null;
        for (let i = state.texts.length - 1; i >= 0; i--) {
            const t = state.texts[i];
            const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
            if(!track) continue; 

            const boxPx = t.currentFullWidth;
            const tX = cycleToPx(t.cycle);
            const tY_Absolute = track.centerY + t.renderY; 
            const hitH = t.renderedHeight;
            const hitBase = t.size;

            if (t.zoomLevel === 1 && t.isSticky && mx >= tX && mx <= tX + 16 && my <= tY_Absolute && my >= tY_Absolute - t.size) {
                t.collapsed = !t.collapsed;
                t.baseCycleWidth = undefined; 
                render();
                return; 
            }

            if (mx >= tX && mx <= tX + boxPx && my <= tY_Absolute + (t.isSticky ? hitH - t.size : 0) && my >= tY_Absolute - hitBase) { 
                hit = t; break; 
            }
        }
        if (hit) {
            state.selectedTextId = hit.id;
            isDraggingText = true; 
            const hitTrack = state.flatTracks.find(tr => tr.node.id === hit.trackId);
            dragOffset = { 
                x: mx - cycleToPx(hit.cycle), 
                y: my - (hitTrack.centerY + hit.renderY) 
            };
        } else {
            state.selectedTextId = null;
            const bTrack = state.flatTracks.find(tr => tr.node.id === state.boundTrackId);
            if(bTrack) {
                let relY = my - bTrack.centerY;
                relY = Math.max(20, relY); 
                startTextEdit(e.clientX - rect.left, e.clientY - rect.top, relY, bTrack.node.id);
            }
        }
        render(); return;
    }
});

waveContainer.addEventListener('mousemove', (e) => {
    // 【新增】处理智能填充拖拽中
    if (state.fill && state.fill.dragging) {
        const rect = waveContainer.getBoundingClientRect();
        const mx = e.clientX - rect.left + state.offsetX;
        state.fill.currentC = Math.floor(pxToCycle(mx));
        // 只允许向右拖拽填充
        state.fill.currentC = Math.max(state.fill.hovered.end, Math.min(state.cycles - 1, state.fill.currentC));
        render();
        return;
    }

    if (state.mode === 'text' && isDraggingText && state.selectedTextId) {
        const rect = waveContainer.getBoundingClientRect();
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if (t) {
            const track = state.flatTracks.find(tr => tr.node.id === t.trackId);
            if (track) {
                const newAbsoluteX = (e.clientX - rect.left + state.offsetX) - dragOffset.x;
                t.cycle = pxToCycle(newAbsoluteX);
                const absoluteMy = e.clientY - rect.top + state.offsetY - state.topMargin;
                t.y = absoluteMy - track.centerY - dragOffset.y; 
                render();
            }
        }
    }

    // 【新增】侦测鼠标是否悬浮在"格子"右下角
    if (state.mode === 'wave' && state.measureMode === 'IDLE' && !state.fill.dragging) {
        const rect = waveContainer.getBoundingClientRect();
        // mx 和 my 是带有滚动偏移的“绝对虚拟坐标”
        const mx = e.clientX - rect.left + state.offsetX;
        const my = e.clientY - rect.top + state.offsetY - state.topMargin;
        const hitTrackIdx = getTrackIdxAtY(my);
        const hitTrack = state.flatTracks[hitTrackIdx];
        
        state.fill.hovered = null;

        if (hitTrack && hitTrack.node.type === 'multi') {
            const sig = hitTrack.node;
            const cycleX = buildCycleMap();
            const cStr = Math.floor(pxToCycle(mx));
            const cLeft = Math.floor(pxToCycle(mx - 10)); // 扩大探测范围，防止鼠标在边缘缝隙时漏判
            
            let block = getMultiBlockAtCycle(sig, cStr) || getMultiBlockAtCycle(sig, cLeft);

            if (block) {
                // 【修复核心】：统一使用绝对虚拟坐标进行比对
                // block.end 是当前格子的最后一个周期，右边缘就是它的坐标 + 一个周期的宽度
                const absRightX = cycleX[block.end] + state.scaleX;
                // hitTrack.centerY 本身就是绝对坐标，波形格子的高度是 24 (centerY-12 到 centerY+12)
                const absBottomY = hitTrack.centerY + 12;
                
                // 鼠标在格子右下角 12x12 像素区域内 (稍微放大了一点判定区，手感更好)
                if (Math.abs(mx - absRightX) <= 12 && Math.abs(my - absBottomY) <= 12) {
                    state.fill.hovered = { tIdx: hitTrackIdx, ...block };
                }
            }
        }

        // 更改鼠标指针样式：悬浮到右下角时变成类似 Excel 的十字光标 (cell)
        if (state.fill.hovered) waveContainer.style.cursor = 'cell';
        else waveContainer.style.cursor = 'crosshair';

        // 避免频繁 render，只有悬浮状态改变时才重绘
        const hid = state.fill.hovered ? `${state.fill.hovered.tIdx}_${state.fill.hovered.end}` : null;
        if (state.fill.lastHoveredId !== hid) {
            state.fill.lastHoveredId = hid;
            render();
        }
    }
});

window.addEventListener('mouseup', () => { 
    isDraggingText = false; 
    
    // 【新增】智能填充松开鼠标时的结算逻辑
    if (state.fill && state.fill.dragging) {
        if (state.fill.currentC > state.fill.hovered.end) {
            const sig = state.flatTracks[state.fill.hovered.tIdx].node;
            // 按照每拍都生成一个新格子的逻辑写入数据
            for (let i = state.fill.hovered.end + 1; i <= state.fill.currentC; i++) {
                sig.data[i] = incrementValue(state.fill.hovered.val, i - state.fill.hovered.end, sig.radix);
            }
        }
        state.fill.dragging = false;
        state.fill.hovered = null;
        state.fill.lastHoveredId = null;
        waveContainer.style.cursor = 'crosshair';
        render();
    }
});

function startTextEdit(screenX, screenY, relY, trackId) {
    state.isEditingText = true;
    textInputOverlay.style.display = 'block';
    textInputOverlay.style.left = `${screenX}px`;
    textInputOverlay.style.top = `${screenY - 14}px`; 
    textInputOverlay.value = ''; 
    textInputOverlay.dataset.px = screenX + state.offsetX;
    textInputOverlay.dataset.relY = relY;
    textInputOverlay.dataset.trackId = trackId;
    setTimeout(() => { textInputOverlay.focus(); }, 10);
}

textInputOverlay.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
        const val = textInputOverlay.value.trim();
        if (val) {
            state.texts.push({ 
                id: 'txt_' + Date.now(), 
                text: val, 
                cycle: pxToCycle(parseFloat(textInputOverlay.dataset.px)), 
                y: parseFloat(textInputOverlay.dataset.relY), 
                trackId: textInputOverlay.dataset.trackId, 
                size: 16, 
                baseScale: state.scaleX, 
                color: '#f1c40f',
                bgColor: '#2d2d30',
                isSticky: false, 
                content: '', 
                collapsed: true
            });
        }
        endTextEdit();
    } else if (e.key === 'Escape') endTextEdit();
});
function endTextEdit() { state.isEditingText = false; textInputOverlay.style.display = 'none'; waveContainer.focus(); render(); }

window.addEventListener('keydown', (e) => {
    if (state.cmdType || state.isModalOpen || state.isEditingText) return;
    const k = e.key.toLowerCase();

    if (k === 't' && state.mode === 'wave') { e.preventDefault(); toggleMode('text'); return; }
    if (k === 'escape' && state.mode === 'text') { e.preventDefault(); toggleMode('wave'); return; }

    if (k === 'm') { e.preventDefault(); toggleMeasureMode(); return; }

    if (state.mode === 'wave' && state.selectedMeasureId) {
        if (k === 'delete' || e.key === 'Backspace') {
            e.preventDefault();
            state.measurements = state.measurements.filter(m => m.id !== state.selectedMeasureId);
            state.selectedMeasureId = null;
            render(); return;
        }
        if (k === 's') { e.preventDefault(); startCmdMode('edit_measure'); return; }
        if (k === 'c') { e.preventDefault(); openAttrModal(); return; }
    }

    if (k === 'delete' || (k === 'd' && lastKey === 'd' && Date.now() - lastKeyTime < 500)) {
        e.preventDefault();
        deleteSelectedSignal();
        lastKey = '';
        return;
    }

    if (k === 'd') { lastKey = 'd'; lastKeyTime = Date.now(); } else { lastKey = ''; }

    if (e.key === '/' && state.mode === 'wave') { e.preventDefault(); startCmdMode('search'); return; }
    if (e.key === ':') { e.preventDefault(); startCmdMode('cmd'); return; }

    if (e.ctrlKey && k === 'g') { e.preventDefault(); groupSelected(); return; }

    if (state.mode === 'text') {
        if (state.selectedTextId) {
            if (k === 'delete' || k === 'x') { state.texts = state.texts.filter(t => t.id !== state.selectedTextId); state.selectedTextId = null; render(); }
            else if (k === 'c') { e.preventDefault(); openAttrModal(); }
        }
        return;
    }

    const sig = state.flatTracks[state.cursorY]?.node;
    if (!sig) return;

    if (k === 'c') { e.preventDefault(); openAttrModal(); return; }

    let moved = false;
    if (e.key === 'ArrowRight' || k === 'l') { state.cursorX = Math.min(state.cycles - 1, state.cursorX + 1); moved = true; }
    if (e.key === 'ArrowLeft'  || k === 'h') { state.cursorX = Math.max(0, state.cursorX - 1); moved = true; }
    if (e.key === 'ArrowDown'  || k === 'j') { state.cursorY = Math.min(state.flatTracks.length - 1, state.cursorY + 1); moved = true; }
    if (e.key === 'ArrowUp'    || k === 'k') { state.cursorY = Math.max(0, state.cursorY - 1); moved = true; }
    
    if (moved) { 
        e.preventDefault(); 
        if (e.key === 'ArrowDown' || e.key === 'ArrowUp' || k === 'j' || k === 'k') {
            const navSig = state.flatTracks[state.cursorY]?.node;
            if (navSig && !e.ctrlKey) {
                state.selectedIds.clear();
                state.selectedIds.add(navSig.id);
            }
        }
        ensureCursorVisible(); 
        return; 
    }

    if (k === 'i') {
        e.preventDefault();
        if (state.gaps.has(state.cursorX)) state.gaps.delete(state.cursorX);
        else state.gaps.add(state.cursorX);
        ensureCursorVisible(); return;
    }

    if (sig.type === 'clock' || sig.type === 'group') return;

    if (k === ' ') {
        e.preventDefault();
        if (state.cursorX > 0) sig.data[state.cursorX] = sig.data[state.cursorX - 1] || 'z';
        state.cursorX = Math.min(state.cycles - 1, state.cursorX + 1);
        ensureCursorVisible(); return;
    }
    if (sig.type === 'single' && ['0', '1', 'x', 'z'].includes(k)) {
        sig.data[state.cursorX] = k; state.cursorX = Math.min(state.cycles - 1, state.cursorX + 1); ensureCursorVisible();
    }
    if (sig.type === 'multi') {
        if (k === 'x' || k === 'z') { sig.data[state.cursorX] = k; state.cursorX = Math.min(state.cycles - 1, state.cursorX + 1); ensureCursorVisible(); }
        else if (k === 's') { e.preventDefault(); startCmdMode('edit'); }
    }
});

waveContainer.addEventListener('wheel', (e) => {
    if (state.isModalOpen || state.isEditingText) return;
    e.preventDefault();

    if (state.mode === 'text' && state.selectedTextId && !e.ctrlKey && !e.shiftKey) {
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if (t) {
            const zoomDelta = e.deltaY > 0 ? -2 : 2; 
            t.size = Math.max(10, Math.min(100, t.size + zoomDelta));
            
            t.baseScale = state.scaleX;
            t.baseCycleWidth = undefined; 
            render();
            return;
        }
    }

    if (e.ctrlKey) {
        const zoomDelta = e.deltaY > 0 ? 0.8 : 1.25;
        const mouseX = e.clientX - waveContainer.getBoundingClientRect().left;
        const absoluteMouseX = mouseX + state.offsetX;
        const ratio = absoluteMouseX / (state.cycles * state.scaleX + state.gaps.size * state.GAP_WIDTH);

        state.scaleX = Math.max(5, Math.min(state.scaleX * zoomDelta, 400));
        const newTotalWidth = state.cycles * state.scaleX + state.gaps.size * state.GAP_WIDTH;
        state.offsetX = Math.max(0, newTotalWidth * ratio - mouseX);
        render();
    } else if (e.shiftKey) { 
        state.offsetX = Math.max(0, state.offsetX + e.deltaY); 
        render();
    } else {
        state.offsetY = Math.max(0, state.offsetY + e.deltaY);
        const rect = waveContainer.getBoundingClientRect();
        const maxScrollY = Math.max(0, state.totalTracksHeight + state.topMargin - rect.height);
        state.offsetY = Math.min(state.offsetY, maxScrollY); 
        renderSignalList(); 
        render();
    }
});

function startCmdMode(type) {
    state.cmdType = type;
    document.getElementById('statusInfo').style.display = 'none'; document.getElementById('statusCmd').style.display = 'flex';
    const label = document.getElementById('cmdLabel');
    
    if (type === 'search') {
        label.innerText = '/SEARCH'; busInput.placeholder = 'Search value...'; busInput.value = '';
    } else if (type === 'cmd') {
        label.innerText = ':CMD'; busInput.placeholder = 'e.g., help, text, wave...'; busInput.value = '';
    } else if (type === 'edit_measure') {
        label.innerText = ':MEASURE_TXT'; 
        const m = state.measurements.find(x => x.id === state.selectedMeasureId);
        busInput.value = m ? m.text : '';
    } else {
        label.innerText = ':EDIT_BUS'; const sig = state.flatTracks[state.cursorY].node;
        busInput.value = sig.data[state.cursorX] && !['x','z'].includes(sig.data[state.cursorX].toLowerCase()) ? sig.data[state.cursorX] : '';
    }
    setTimeout(() => { busInput.focus(); if (type === 'edit' || type === 'edit_measure') busInput.select(); }, 10);
}

busInput.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
        const val = busInput.value.trim();
        if (state.cmdType === 'edit_measure') {
            const m = state.measurements.find(x => x.id === state.selectedMeasureId);
            if (m) m.text = val;
        }
        else if (state.cmdType === 'edit') {
            state.flatTracks[state.cursorY].node.data[state.cursorX] = val;
            state.cursorX = Math.min(state.cycles - 1, state.cursorX + 1);
        } 
        else if (state.cmdType === 'search') {
            const sig = state.flatTracks[state.cursorY].node;
            let found = false;
            const searchStr = val.toLowerCase();
            for (let offset = 1; offset <= state.cycles; offset++) {
                const i = (state.cursorX + offset) % state.cycles;
                const rawVal = sig.data[i] || 'z';
                const parsed = parseDisplayStr(rawVal, sig);
                if (rawVal.toLowerCase().includes(searchStr) || parsed.str.toLowerCase().includes(searchStr)) {
                    state.cursorX = i; found = true; break;
                }
            }
            if (!found) alert('整条轨道未找到: ' + val);
        } 
        else if (state.cmdType === 'cmd') {
            if (val === 'text') toggleMode('text'); 
            else if (val === 'wave') toggleMode('wave');
            else if (val === 'help') { openHelpModal(); }
        }
        endCmdMode(); ensureCursorVisible();
    } else if (e.key === 'Escape') endCmdMode();
});

function endCmdMode() {
    if (state.cmdType === 'cmd' && busInput.value.trim() === 'help') return; 
    state.cmdType = ''; busInput.blur();
    document.getElementById('statusCmd').style.display = 'none'; document.getElementById('statusInfo').style.display = 'flex';
    waveContainer.focus(); render();
}

function openAttrModal() {
    state.isModalOpen = true; attrModal.style.display = 'flex';
    const thickRow = document.getElementById('thicknessRow'); 
    const stickyRow = document.getElementById('stickyRow');
    const contentRow = document.getElementById('contentRow');
    const bgColorRow = document.getElementById('bgColorRow');
    
    if (stickyRow) stickyRow.style.display = 'none';
    if (contentRow) contentRow.style.display = 'none';
    if (bgColorRow) bgColorRow.style.display = 'none';

    if (state.mode === 'wave' && state.selectedMeasureId) {
        document.getElementById('modalTitle').innerText = 'Measure Properties';
        const m = state.measurements.find(x => x.id === state.selectedMeasureId);
        
        document.getElementById('nameRow').style.display = 'flex';
        document.getElementById('modalName').value = m.text || ''; 
        document.getElementById('radixRow').style.display = 'none';
        document.getElementById('colorRow').style.display = 'flex';
        document.getElementById('modalColor').value = m.color;
        if (thickRow) {
            thickRow.style.display = 'flex';
            document.getElementById('modalThickness').value = m.thickness;
        }
    } 
    else if (state.mode === 'text' && state.selectedTextId) {
        document.getElementById('modalTitle').innerText = 'Text / Note Properties';
        const t = state.texts.find(x => x.id === state.selectedTextId);
        
        document.getElementById('nameRow').style.display = 'flex'; 
        document.getElementById('modalName').value = t.text || '';
        document.getElementById('colorRow').style.display = 'flex';
        document.getElementById('modalColor').value = t.color;
        
        if (bgColorRow) {
            bgColorRow.style.display = 'flex';
            document.getElementById('modalBgColor').value = t.bgColor || '#2d2d30';
        }

        document.getElementById('radixRow').style.display = 'none'; 
        if (thickRow) thickRow.style.display = 'none'; 
        
        if (stickyRow) stickyRow.style.display = 'flex';
        if (contentRow) contentRow.style.display = 'flex';
        document.getElementById('modalIsSticky').checked = !!t.isSticky;
        document.getElementById('modalTextContent').value = t.content || '';
    } 
    else {
        const sig = state.flatTracks[state.cursorY].node;
        document.getElementById('modalTitle').innerText = sig.type === 'group' ? 'Group Properties' : 'Signal Properties';
        
        document.getElementById('nameRow').style.display = 'flex';
        document.getElementById('modalName').value = sig.name;
        document.getElementById('colorRow').style.display = 'flex';
        document.getElementById('modalColor').value = sig.color;
        document.getElementById('modalRadix').value = sig.radix || 'hex';
        document.getElementById('radixRow').style.display = (sig.type === 'multi') ? 'flex' : 'none';
        if (thickRow) thickRow.style.display = 'none'; 
    }
    setTimeout(() => document.getElementById('modalName').focus(), 10);
}

function closeAttrModal() { state.isModalOpen = false; attrModal.style.display = 'none'; waveContainer.focus(); }

function applyAttrModal() {
    if (state.mode === 'wave' && state.selectedMeasureId) {
        const m = state.measurements.find(x => x.id === state.selectedMeasureId);
        if (m) {
            m.text = document.getElementById('modalName').value.trim() || m.text; 
            m.color = document.getElementById('modalColor').value;
            const thickVal = parseInt(document.getElementById('modalThickness').value);
            if (!isNaN(thickVal) && thickVal >= 1) m.thickness = thickVal;
        }
    } 
    else if (state.mode === 'text' && state.selectedTextId) {
        const t = state.texts.find(x => x.id === state.selectedTextId);
        if(t) {
            t.text = document.getElementById('modalName').value.trim() || t.text;
            t.color = document.getElementById('modalColor').value;
            t.bgColor = document.getElementById('modalBgColor').value;
            t.isSticky = document.getElementById('modalIsSticky').checked;
            t.content = document.getElementById('modalTextContent').value;
            
            t.baseScale = state.scaleX;    
            t.baseCycleWidth = undefined; 
        }
    }
    else {
        const sig = state.flatTracks[state.cursorY].node;
        sig.name = document.getElementById('modalName').value.trim() || sig.name;
        sig.color = document.getElementById('modalColor').value;
        if (sig.type === 'multi') sig.radix = document.getElementById('modalRadix').value;
        refreshAll();
    }
    closeAttrModal(); render();
}

function openHelpModal() {
    state.isModalOpen = true; 
    state.cmdType = ''; busInput.blur();
    document.getElementById('statusCmd').style.display = 'none'; document.getElementById('statusInfo').style.display = 'flex';
    helpModal.style.display = 'flex';
}

function closeHelpModal() { state.isModalOpen = false; helpModal.style.display = 'none'; waveContainer.focus(); }

document.getElementById('attrModal').addEventListener('keydown', (e) => {
    if (e.key === 'Enter' && e.target.id !== 'modalTextContent') { applyAttrModal(); }
    else if (e.key === 'Enter' && e.ctrlKey) { applyAttrModal(); }
});
// ==========================================
// 【新增】导出与导入功能 (JSON 序列化)
// ==========================================

function exportWaveform() {
    // 提取需要持久化的核心数据
    const exportData = {
        cycles: state.cycles,
        scaleX: state.scaleX,
        tree: state.tree,
        texts: state.texts,
        measurements: state.measurements,
        gaps: Array.from(state.gaps) // Set 对象不能直接转 JSON，转成数组
    };

    // 转换为格式化的 JSON 字符串
    const dataStr = JSON.stringify(exportData, null, 2);
    const blob = new Blob([dataStr], { type: "application/json" });
    const url = URL.createObjectURL(blob);

    // 动态创建 a 标签触发下载
    const a = document.createElement('a');
    a.href = url;
    a.download = `digi_wave_${new Date().toISOString().slice(0,10).replace(/-/g,"")}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
}

function importWaveform() {
    // 触发隐藏的文件输入框
    document.getElementById('fileInput').click();
}

function handleFileImport(event) {
    const file = event.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = function(e) {
        try {
            const importedData = JSON.parse(e.target.result);

            // 恢复数据
            state.cycles = importedData.cycles || 100;
            state.scaleX = importedData.scaleX || 50;
            state.tree = importedData.tree || [];
            state.texts = importedData.texts || [];
            state.measurements = importedData.measurements || [];
            state.gaps = new Set(importedData.gaps || []); // 将数组恢复为 Set

            // 重置 UI 状态，防止读取旧数据时越界或持有不存在的 ID
            state.selectedIds.clear();
            state.selectedTextId = null;
            state.selectedMeasureId = null;
            state.boundTrackId = null;
            state.fill.hovered = null;
            state.fill.dragging = false;
            state.cursorX = 0;
            state.cursorY = 0;
            state.offsetX = 0;
            state.offsetY = 0;
            state.measureMode = 'IDLE';
            state.tempMeasurePoint = null;
            if (btnMeasure) btnMeasure.classList.remove('active');

            // 彻底重绘
            refreshAll();
            
            // 如果导入成功，控制台提示一下
            console.log("Waveform imported successfully.");

        } catch (err) {
            alert("读取失败：文件损坏或格式不正确！\n" + err.message);
        }
        
        // 清空 input，保证用户下次还能选中同一个文件触发 onchange
        event.target.value = '';
    };
    
    reader.readAsText(file);
}
// ==========================================
// 【新增】初始化时自动加载默认配置
// ==========================================
function loadDefaultWaveform() {
    fetch('digi_wave.json')
        .then(response => {
            if (!response.ok) {
                throw new Error(`HTTP error! status: ${response.status}`);
            }
            return response.json();
        })
        .then(importedData => {
            // 解析成功，覆盖当前状态
            state.cycles = importedData.cycles || 100;
            state.scaleX = importedData.scaleX || 50;
            state.tree = importedData.tree || [];
            state.texts = importedData.texts || [];
            state.measurements = importedData.measurements || [];
            state.gaps = new Set(importedData.gaps || []);

            // 重置 UI 交互状态
            state.selectedIds.clear();
            state.selectedTextId = null;
            state.selectedMeasureId = null;
            state.boundTrackId = null;
            state.fill.hovered = null;
            state.fill.dragging = false;
            state.cursorX = 0;
            state.cursorY = 0;
            state.offsetX = 0;
            state.offsetY = 0;
            state.measureMode = 'IDLE';
            state.tempMeasurePoint = null;

            refreshAll();
            console.log("Default digi_wave.json loaded successfully.");
        })
        .catch(e => {
            // 如果文件不存在，或者因为 file:// 协议被拦截，就回退到使用 JS 里默认定义的初始状态
            console.log("Could not load default digi_wave.json (maybe running via file:// or file missing). Using default state.", e.message);
            refreshAll(); 
        });
}

// 执行初始化
waveContainer.focus();
resizeCanvas();
loadDefaultWaveform(); // 替代了原来的 refreshAll()，在请求结果出来后再渲染