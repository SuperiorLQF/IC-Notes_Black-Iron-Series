// Persistent fills live on signals, independently of their values and anchors.
let paintMessage = '';
function clearRowSelection() {
    state.selectedIds.clear();state.selectedTextId=state.selectedConnId=state.selectedMeasureId=null;
    state.boundTrackId=null;state.mode='VIEW';state.subMode='NORMAL';state.pendingVal=null;
    editorSelection=null;editorGesture=null;textInputOverlay.style.display='none';busValueInput.blur();paintMessage='';updateUI();
}
function togglePaintMode() {
    state.mode='EDIT';state.subMode=state.subMode==='PAINT'?'NORMAL':'PAINT';
    state.pendingVal=null;textInputOverlay.style.display='none';busValueInput.blur();paintMessage='';updateUI();waveContainer.focus();
}
function updateFillControls() {
    document.getElementById('fillColorInput').disabled=document.getElementById('fillColorMode').value!=='custom';
    paintMessage='';updateEditorHelp();
}
function replaceFillRange(sig,start,end,additions=[]) {
    const remaining=[];
    for(const fill of sig.fills||[]) {
        if(fill.end<=start || fill.start>=end)remaining.push(fill);
        else {
            if(fill.start<start)remaining.push({...fill,end:start});
            if(fill.end>end)remaining.push({...fill,start:end});
        }
    }
    sig.fills=[...remaining,...additions].sort((a,b)=>a.start-b.start);
    if(!sig.fills.length)delete sig.fills;
}
function paintSignalSegment(sig,time) {
    paintMessage='';
    const boundaries=[...new Set([0,...signalBoundaryTimes(sig)])].sort((a,b)=>a-b);
    let start=0,end=null;
    for(const boundary of boundaries) {if(boundary<=time+1e-6)start=boundary;else {end=boundary;break;}}
    if(end===null) {paintMessage='这段没有结束边沿：先按 Esc，再用 K 添加结束锚点。';updateEditorHelp();return;}
    const value=getSignalValueAtTime(sig,(start+end)/2);
    if(sig.type==='single' && !['0','1'].includes(value)) {paintMessage='X/Z 使用自身状态样式；油漆桶用于 0/1 和 Bus。';updateEditorHelp();return;}
    const mode=document.getElementById('fillColorMode').value;
    const color=mode==='default'?'default':document.getElementById('fillColorInput').value;
    replaceFillRange(sig,start,end,mode==='clear'?[]:[{start,end,color}]);
    state.selectedIds=new Set([sig.id]);state.cursorT=start;updateUI();
}
function fillDisplayColor(sig,fill) {
    if(state.printMode)return '#d8d8d8';
    let hex=fill.color==='default'?(sig.color||'#70f5ff'):fill.color;
    if(/^#[0-9a-f]{3}$/i.test(hex))hex='#'+hex.slice(1).split('').map(c=>c+c).join('');
    if(!/^#[0-9a-f]{6}$/i.test(hex))hex='#70f5ff';
    let rgb=[1,3,5].map(index=>parseInt(hex.slice(index,index+2),16));
    if(fill.color==='default')rgb=rgb.map(channel=>Math.round(channel+(255-channel)*.55));
    return `rgba(${rgb.join(',')},0.35)`;
}
function captureFills(sig,start,end) {
    return (sig.fills||[]).filter(f=>f.start<end && f.end>start).map(f=>({...f,start:Math.max(f.start,start)-start,end:Math.min(f.end,end)-start}));
}
function pasteFills(sig,at,fills) {
    if(fills.length)sig.fills=[...(sig.fills||[]),...fills.map(f=>({...f,start:at+f.start,end:at+f.end}))].sort((a,b)=>a.start-b.start);
}
function renderSignalFills(sig,track) {
    if(!sig.fills?.length)return;
    const mid=track.centerY+state.topMargin-state.offsetY,high=mid-14,low=mid+14;
    const events=sig.data?.length?sig.data:[{t:0,val:sig.type==='multi'?'':'z'}];
    ctx.save();
    for(const fill of sig.fills) {
        for(let i=0;i<events.length;i++) {
            const segmentStart=events[i].t,segmentEnd=events[i+1]?.t??(fill.end+12/state.scaleX);
            const start=Math.max(fill.start,segmentStart),end=Math.min(fill.end,segmentEnd);
            if(end<=start)continue;
            const left=timeToPx(start)-state.offsetX,right=timeToPx(end)-state.offsetX;
            if(right<0 || left>canvas.clientWidth)continue;
            const value=events[i].val;
            if(sig.type==='single' && !['0','1'].includes(value))continue;
            ctx.save();
            if(sig.type==='multi') {
                // Clip at real bus transitions, not at an internal K marker.
                const x1=timeToPx(segmentStart)-state.offsetX,x2=timeToPx(segmentEnd)-state.offsetX;
                const slope=Math.min(6,(x2-x1)/2);
                ctx.beginPath();ctx.moveTo(x1,mid);ctx.lineTo(x1+slope,high);ctx.lineTo(x2-slope,high);ctx.lineTo(x2,mid);ctx.lineTo(x2-slope,low);ctx.lineTo(x1+slope,low);ctx.closePath();ctx.clip();
            }
            ctx.fillStyle=fillDisplayColor(sig,fill);
            const y=sig.type==='multi'||value==='1'?high:mid;
            const height=sig.type==='multi'?28:14;
            ctx.fillRect(left,y,right-left,height);ctx.restore();
        }
    }
    ctx.restore();
}
