const {chromium}=require('playwright');
const {PNG}=require('pngjs');
const http=require('http'),fs=require('fs'),path=require('path'),assert=require('assert');
const root=path.resolve(__dirname,'../docs/digiwave');
(async()=>{
const server=http.createServer((req,res)=>{let name=decodeURIComponent(req.url.split('?')[0]);if(name==='/')name='/index.html';const p=path.join(root,name);if(!p.startsWith(root+'/')){res.writeHead(403).end();return;}fs.readFile(p,(err,data)=>{if(err){res.writeHead(404).end();return;}res.setHeader('Content-Type',p.endsWith('.js')?'text/javascript':p.endsWith('.css')?'text/css':p.endsWith('.json')?'application/json':'text/html');res.end(data);});});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const browser=await chromium.launch({executablePath:process.env.CHROMIUM_PATH || '/usr/bin/chromium',headless:true,args:['--no-sandbox']});
try {
 const page=await browser.newPage({viewport:{width:1500,height:900},deviceScaleFactor:2});const errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.addInitScript(()=>{Object.defineProperty(crypto,'randomUUID',{value:undefined,configurable:true});});
 await page.goto(`http://127.0.0.1:${server.address().port}/`);await page.waitForFunction(()=>projectHistory.initialized);
 console.log('default loaded',await page.evaluate(()=>state.tree.length));
 await page.evaluate(()=>{
  state.tree=[{id:'a',name:'clk',type:'single',data:[{t:0,val:'0'},{t:10,val:'1'},{t:20,val:'0'},{t:30,val:'1'}],color:'#5cf',thickness:2},{id:'b',name:'data',type:'single',data:[{t:0,val:'0'},{t:10,val:'1'},{t:20,val:'0'}],color:'#fc5',thickness:2}];state.texts=[];state.measurements=[];state.connections=[];state.scaleX=10;state.offsetX=state.offsetY=0;updateUI();initializeHistory();
 });
 const baseline=await page.evaluate(()=>projectSnapshot());
 const helpPopup=page.waitForEvent('popup');await page.locator('#handbookLink').click();const handbook=await helpPopup;
 await handbook.waitForLoadState('domcontentloaded');assert.equal(await handbook.title(),'DigiWave Handbook · 操作手册');
 await handbook.locator('nav a[href="#clock"]').click();assert(handbook.url().endsWith('#clock'));
 assert(await handbook.locator('#clock').textContent().then(t=>t.includes('Duty')));
 assert.equal(await page.evaluate(()=>projectSnapshot()),baseline);await handbook.close();
 console.log('GUI Handbook link opens a separate page, anchors work, project unchanged PASS');

 await page.evaluate(()=>{state.selectedIds=new Set(['a']);state.mode='EDIT';state.subMode='NORMAL';updateUI();});
 assert(await page.locator('#editorHelp').textContent().then(t=>t.includes('⌫ Backspace')&&t.includes('后续内容前移')&&t.includes('拖动')));
 assert.equal(await page.locator('#editorHelp kbd').filter({hasText:/^V$/}).count(),0);
 await page.evaluate(()=>{state.tree.push({id:'hint-bus',type:'multi',name:'bus',color:'#a5f',radix:'hex',data:[{t:0,val:'0'}]});state.selectedIds=new Set(['hint-bus']);updateUI();});
 assert.equal(await page.locator('#editorHelp kbd').filter({hasText:/^V$/}).count(),1);
 await page.locator('#waveContainer').focus();await page.keyboard.press('v');
 assert(await page.locator('#editorHelp').textContent().then(t=>t.includes('BUS VALUE')&&t.includes('删除输入框中的字符')));
 assert.equal(await page.locator('#editorHelp kbd').filter({hasText:/^R$/}).count(),0);
 await page.keyboard.press('Escape');
 await page.evaluate(()=>{state.tree=state.tree.filter(s=>s.id!=='hint-bus');state.selectedIds=new Set(['a']);state.mode='INSERT';state.subMode='NORMAL';state.pendingVal='1';updateUI();});
 assert(await page.locator('#editorHelp').textContent().then(t=>t.includes('␣ Space')&&t.includes('插入终点')));
 await page.keyboard.press('r');assert(await page.locator('#editorHelp').textContent().then(t=>t.includes('片段起始边沿')));await page.keyboard.press('Escape');
 await page.keyboard.press('Enter');assert(await page.locator('#editorHelp').textContent().then(t=>t.includes('DURATION')&&t.includes('关闭时间输入面板')));await page.locator('#durationInput').press('Escape');
 await page.evaluate(()=>{state.mode='VIEW';state.pendingVal=null;state.subMode='NORMAL';updateUI();initializeHistory();});
 assert.equal(await page.evaluate(()=>projectSnapshot()),baseline);
 console.log('Bottom hints match Binary/Bus Edit, numeric input, Insert, Repeat and duration dialog PASS');
 await page.waitForFunction(()=>Math.abs(canvas.clientHeight-waveContainer.clientHeight)<=1);
 const viewBlocks=await page.evaluate(()=>{
  state.selectedIds=new Set(['a']);state.mode='VIEW';state.cursorT=10;
  const original=ctx.strokeRect;let blocks=0;
  ctx.strokeRect=function(...args){if(args[0]===95 && args[2]===10 && this.lineWidth===2 && this.shadowBlur===8)blocks++;return original.apply(this,args);};
  try{render();return blocks;}finally{ctx.strokeRect=original;}
 });assert.equal(viewBlocks,1);console.log('Bright cursor centred on transition PASS');

 await page.evaluate(()=>{state.selectedIds=new Set(['a']);state.mode='INSERT';state.pendingVal='0';state.cursorT=30;lastDurationValue='1us';});
 await page.locator('#waveContainer').focus();await page.keyboard.press('Space');
 assert.equal(await page.evaluate(()=>state.cursorT),1030);console.log('unit reuse PASS');
 await page.keyboard.press('Control+z');assert.equal(await page.evaluate(()=>projectSnapshot()),baseline);
 await page.keyboard.press('Control+Shift+z');assert.equal(await page.evaluate(()=>state.tree[0].data.at(-1).t),1030);console.log('undo/redo PASS');
 await page.evaluate(()=>{undoProject();state.mode='VIEW';});
 const point=await page.evaluate(()=>{const r=waveContainer.getBoundingClientRect(),tr=state.flatTracks[0];return{x:r.left+100,y:r.top+tr.centerY+state.topMargin};});
 // Click far beyond the old 10px hit radius: always choose the nearer edge.
 await page.mouse.click(point.x+35,point.y);
 assert.equal(await page.evaluate(()=>state.cursorT),10);
 await page.mouse.click(point.x+65,point.y);
 assert.equal(await page.evaluate(()=>state.cursorT),20);
 await page.mouse.click(point.x+50,point.y);
 assert.equal(await page.evaluate(()=>state.cursorT),10);
 await page.mouse.click(point.x+400,point.y);
 assert.equal(await page.evaluate(()=>state.cursorT),30);
 await page.locator('#waveContainer').focus();await page.keyboard.press('ArrowRight');
 assert.equal(await page.evaluate(()=>state.cursorT),30);
 await page.evaluate(()=>{state.cursorT=15;updateUI();});
 assert.equal(await page.evaluate(()=>state.cursorT),10);
 console.log('Nearest edge selection, midpoint tie and end boundary PASS');
 const viewSnapshot=await page.evaluate(()=>projectSnapshot());
 await page.mouse.dblclick(point.x+40,point.y);
 assert.equal(await page.evaluate(()=>projectSnapshot()),viewSnapshot);console.log('View double-click preserves waveform PASS');
 await page.mouse.move(point.x,point.y);await page.mouse.down();await page.mouse.move(point.x+40,point.y,{steps:5});await page.mouse.up();
 assert.equal(await page.evaluate(()=>projectSnapshot()),viewSnapshot);console.log('View drag preserves waveform PASS');
 await page.evaluate(()=>{state.selectedIds=new Set(['a']);});await page.locator('#waveContainer').focus();await page.keyboard.press('e');
 assert.equal(await page.evaluate(()=>state.mode),'EDIT');
 await page.mouse.move(point.x,point.y);await page.mouse.down();await page.mouse.move(point.x+40,point.y,{steps:5});await page.mouse.up();
 assert.equal(await page.evaluate(()=>state.tree[0].data[1].t),14);await page.keyboard.press('Control+z');assert.equal(await page.evaluate(()=>state.tree[0].data[1].t),10);console.log('edge drag + undo PASS');
 // Fixed 4 ns grid: 14.3 ns must land on 16 ns.
 await page.evaluate(()=>{document.getElementById('gridStep').value='4';state.selectedIds=new Set(['a']);});
 await page.keyboard.press('e');await page.mouse.move(point.x,point.y);await page.mouse.down();await page.mouse.move(point.x+43,point.y,{steps:4});await page.mouse.up();
 assert.equal(await page.evaluate(()=>state.tree[0].data[1].t),16);await page.keyboard.press('Control+z');
 // Reference grid: 13 ns is 20 px from its 15 ns gridline, but still must snap there.
 await page.evaluate(()=>{state.tree[1].data=[{t:0,val:'0'},{t:15,val:'1'},{t:25,val:'0'}];document.getElementById('gridStep').value='1';state.selectedIds=new Set(['a']);updateUI();});
 await page.locator('#snapSelect').selectOption('b');await page.locator('#waveContainer').focus();await page.keyboard.press('e');
 await page.mouse.move(point.x,point.y);await page.mouse.down();await page.mouse.move(point.x+30,point.y,{steps:4});await page.mouse.up();
 assert.equal(await page.evaluate(()=>state.tree[0].data[1].t),15);
 await page.keyboard.press('Control+z');
 await page.evaluate(()=>{state.tree[1].data=[{t:0,val:'0'},{t:10,val:'1'},{t:20,val:'0'}];state.snapTargetId=null;updateUI();});
 await page.locator('#snapSelect').selectOption('');
 console.log('Edit edge drag snaps to fixed grid and strictly to reference edges PASS');
 await page.keyboard.down('Shift');await page.mouse.move(point.x-80,point.y);await page.mouse.down();await page.mouse.move(point.x+60,point.y+60,{steps:5});await page.mouse.up();await page.keyboard.up('Shift');
 assert.equal(await page.evaluate(()=>editorSelection.ids.length),2);
 await page.keyboard.press('Control+c');await page.evaluate(()=>{state.cursorT=50;});await page.keyboard.press('Control+v');
 assert(await page.evaluate(()=>state.tree[0].data.some(e=>e.t===50)));console.log('cross-track selection + paste PASS');
 await page.evaluate(()=>{writeBackup();validateProject(projectData());});
 const recoverySnapshot=await page.evaluate(()=>{markProjectSaved();return projectSnapshot();});page.once('dialog',d=>d.accept());await page.reload(); // handle restore after fetch
 await page.waitForFunction(()=>projectHistory.initialized);assert.equal(await page.evaluate(()=>projectSnapshot()),recoverySnapshot);console.log('backup recovery PASS');
 assert.equal(await page.evaluate(()=>parseDisplayStr('0xFFFFFFFFFFFFFFFF',{radix:'dec'}).str),'18446744073709551615');console.log('64-bit bus display PASS');
 const before=await page.evaluate(()=>projectSnapshot());
 assert(await page.evaluate(()=>{try{validateProject({tree:[{id:'x',name:'x',type:'single',data:[{t:-1,val:'1'}]}]});return false;}catch{return true;}}));
 assert.equal(await page.evaluate(()=>projectSnapshot()),before);console.log('invalid project rejected PASS');
 const originalSignals = await page.evaluate(()=>JSON.stringify(state.tree));
 await page.evaluate(()=>{state.selectedIds.clear();});
 await page.getByTitle('添加信号',{exact:true}).hover();await page.locator('#addClockButton').click();
 await page.locator('#clockPeriod').fill('10');await page.locator('#clockDuty').fill('25');await page.locator('#clockCount').fill('4');await page.locator('#clockStart').fill('102');
 await page.locator('#clockAddButton').click();
 assert(await page.evaluate(()=>state.tree.at(-1).data.some(e=>e.t===104.5 && e.val==='0')));
 assert.equal(await page.evaluate(()=>state.tree.at(-1).data.at(-1).t),142);
 assert.equal(await page.evaluate(()=>JSON.stringify(state.tree.slice(0,-1))),originalSignals);
 assert.equal(await page.locator('#clockModal').isVisible(),false);
 await page.locator('#waveContainer').focus();await page.keyboard.press('Control+z');
 assert.equal(await page.evaluate(()=>JSON.stringify(state.tree)),originalSignals);
 await page.keyboard.press('Control+Shift+z');
 console.log('Add Clock menu, new signal without selection, exact timing and undo/redo PASS');
 const download=page.waitForEvent('download');await page.evaluate(()=>exportWaveform());const saved=await download;
 const exportPath=await saved.path();const exported=JSON.parse(fs.readFileSync(exportPath,'utf8'));assert.equal(exported.formatVersion,1);assert.equal(exported.tree.length,3);
 assert.equal(await page.evaluate(()=>projectIsDirty()),false);console.log('JSON export + saved marker PASS');
 await page.evaluate(()=>{state.scaleX=10;state.offsetX=0;updateUI();});
 await page.keyboard.down('Alt');await page.mouse.click(point.x,point.y);await page.mouse.click(point.x+50,point.y);await page.keyboard.up('Alt');
 assert.equal(await page.evaluate(()=>measurementCursors.length),2);console.log('measurement cursors PASS');
 await page.screenshot({path:'/tmp/digiwave-editor.png'});
 await page.evaluate(()=>{state.tree=[{id:'g',name:'group',type:'group',expanded:true,children:[{id:'c',name:'child',type:'single',data:[{t:0,val:'0'}]}]}];updateUI();moveNode('g','c');});
 assert.equal(await page.evaluate(()=>state.tree[0].id),'g');assert.equal(await page.evaluate(()=>state.tree[0].children[0].id),'c');console.log('group descendant drag guard PASS');
 await page.evaluate(()=>{state.tree=[{id:'zoom',name:'zoom',type:'single',data:[{t:0,val:'0'},{t:100,val:'1'}]}];state.texts=[];state.measurements=[];state.connections=[];state.selectedIds.clear();state.mode='VIEW';editorSelection={a:20,b:30,ids:['zoom']};updateUI();});
 await page.locator('#waveContainer').focus();await page.keyboard.press('f');
 assert(Math.abs(await page.evaluate(()=>waveContainer.clientWidth/state.scaleX)-100)<1e-8);
 assert.equal(await page.evaluate(()=>state.offsetX),0);
 await page.locator('#fitButton').click();assert.equal(await page.locator('#fitButton svg').count(),1);
 const zoomBox=await page.locator('#waveContainer').boundingBox();await page.mouse.move(zoomBox.x+zoomBox.width/2,zoomBox.y+100);
 await page.keyboard.down('Control');for(let i=0;i<20;i++)await page.mouse.wheel(0,100);await page.keyboard.up('Control');
 await page.waitForTimeout(150);
 assert(Math.abs(await page.evaluate(()=>waveContainer.clientWidth/state.scaleX)-120)<1e-8);
 assert.equal(await page.evaluate(()=>state.offsetX),0);
 await page.mouse.wheel(10000,0);await page.waitForTimeout(100);assert.equal(await page.evaluate(()=>state.offsetX),0);
 await page.evaluate(()=>{document.getElementById('scaleInput').value='0.001';applyScaleModal();});
 assert(Math.abs(await page.evaluate(()=>waveContainer.clientWidth/state.scaleX)-120)<1e-8);
 await page.setViewportSize({width:1800,height:900});await page.waitForTimeout(100);
 assert(await page.evaluate(()=>waveContainer.clientWidth/state.scaleX)<=120.000001);
 console.log('F/button fit 100%, zoom-out limited to 120%, pan/manual scale/resize limits PASS');
 await page.evaluate(()=>{state.tree=[];state.texts=[];state.measurements=[];state.connections=[];state.selectedIds.clear();updateUI();});
 await page.getByTitle('添加信号',{exact:true}).hover();await page.locator('#addClockButton').click();
 await page.locator('#clockPeriod').fill('0');await page.locator('#clockAddButton').click();
 assert.equal(await page.evaluate(()=>state.tree.length),0);assert(await page.locator('#clockError').textContent());
 await page.locator('#clockPeriod').fill('10');await page.locator('#clockStart').fill('0');await page.locator('#clockCount').fill('1');
 await page.locator('#clockAddButton').click();
 assert.equal(await page.evaluate(()=>state.tree.length),1);assert.equal(await page.evaluate(()=>state.tree[0].type),'single');
 assert.equal(await page.evaluate(()=>state.tree[0].data.at(-1).t),10);
 console.log('Empty project clock creation and invalid parameter protection PASS');
 for (const [unit, value, expected] of [['ps','500',0.5],['ns','2',2],['us','0.25',250],['ms','0.001',1000]]) {
  const previousCount=await page.evaluate(()=>state.tree.length);
  await page.getByTitle('添加信号',{exact:true}).hover();await page.locator('#addClockButton').click();
  await page.locator('#clockPeriod').fill(value);await page.locator('#clockPeriodUnit').selectOption(unit);
  await page.locator('#clockStart').fill('1000');await page.locator('#clockStartUnit').selectOption('ps');
  await page.locator('#clockCount').fill('2');await page.locator('#clockAddButton').click();
  assert.equal(await page.evaluate(()=>state.tree.length),previousCount+1);
  assert.equal(await page.evaluate(()=>state.tree.at(-1).data.at(-1).t),1+2*expected);
 }
 assert.equal(await page.evaluate(()=>new Set(state.tree.map(s=>s.id)).size),await page.evaluate(()=>state.tree.length));
 console.log('Numeric time inputs, ps/ns/us/ms conversion and creation without crypto.randomUUID PASS');
 await page.getByTitle('添加信号',{exact:true}).hover();await page.locator('#addClockButton').click();
 const beforeEnter=await page.evaluate(()=>state.tree.length);
 await page.locator('#clockPeriod').fill('');await page.locator('#clockAddButton').click();
 assert.equal(await page.evaluate(()=>state.tree.length),beforeEnter);assert(await page.locator('#clockError').isVisible());
 await page.locator('#clockPeriod').fill('1e-3');await page.locator('#clockPeriodUnit').selectOption('ms');
 await page.locator('#clockPeriod').press('Enter');assert.equal(await page.evaluate(()=>state.tree.length),beforeEnter+1);
 console.log('Direct Add click, blank-value feedback and Enter creation PASS');


 // Existing project format: annotations bind by signal ID + edge time.
 await page.evaluate(()=>{
  state.tree=['attach-a','attach-b'].map(id=>({id,name:id,type:'single',color:'#ff0000',thickness:2,data:[{t:0,val:'0'},{t:10,val:'1'},{t:20,val:'0'}]}));
  state.connections=[{id:'cross',sigId1:'attach-a',t1:10,sigId2:'attach-b',t2:10,text:'cross',color:'#f00',thickness:2},{id:'same',sigId1:'attach-a',t1:20,sigId2:'attach-a',t2:10,text:'same',color:'#f00',thickness:2}];
  state.measurements=[{id:'measure',sigId1:'attach-a',t1:10,sigId2:'attach-a',t2:20,text:'delta',color:'#fa0',thickness:1}];
  state.texts=[];state.selectedIds=new Set(['attach-a']);state.snapTargetId=null;state.mode='EDIT';state.subMode='NORMAL';state.scaleX=10;state.offsetX=state.offsetY=0;document.getElementById('gridStep').value='1';editorSelection=null;updateUI();
 });
 const attachmentBefore=await page.evaluate(()=>projectSnapshot());
 const attachedPoint=await page.evaluate(()=>{const r=waveContainer.getBoundingClientRect(),track=state.flatTracks[0];return{x:r.left+100,y:r.top+track.centerY+state.topMargin};});
 await page.mouse.move(attachedPoint.x,attachedPoint.y);await page.mouse.down();await page.mouse.move(attachedPoint.x+40,attachedPoint.y,{steps:4});
 assert.deepEqual(await page.evaluate(()=>[state.connections[0].t1,state.connections[0].t2,state.connections[1].t1,state.connections[1].t2,state.measurements[0].t1,state.measurements[0].t2]),[14,10,20,14,14,20]);
 await page.mouse.up();await page.locator('#waveContainer').focus();await page.keyboard.press('Control+z');assert.equal(await page.evaluate(()=>projectSnapshot()),attachmentBefore);
 await page.keyboard.press('Control+Shift+z');assert.equal(await page.evaluate(()=>state.connections[0].t1),14);
 await page.evaluate(()=>{state.selectedIds=new Set(['attach-a']);updateUI();});await page.keyboard.press('e');
 assert.equal(await page.evaluate(()=>state.mode),'EDIT');
 await page.mouse.move(attachedPoint.x+40,attachedPoint.y);await page.mouse.down();await page.mouse.move(attachedPoint.x+60,attachedPoint.y,{steps:4});
 assert.equal(await page.evaluate(()=>state.connections[0].t1),16);
 await page.keyboard.press('Escape');await page.mouse.up();
 assert.equal(await page.evaluate(()=>state.connections[0].t1),14);assert.equal(await page.evaluate(()=>state.tree[0].data[1].t),14);
 await page.evaluate(()=>{insertAndPush(state.tree[0],0,5,'0');updateUI();});
 assert.deepEqual(await page.evaluate(()=>[state.connections[0].t1,state.connections[0].t2,state.measurements[0].t1]),[19,10,19]);
 console.log('Attached connections and measurements follow edges live, undo/redo, Escape and insertion PASS');

 const printPixels=await page.evaluate(()=>{
  state.tree=[{id:'print-single',name:'single',type:'single',color:'#ff0000',data:[{t:0,val:'x'},{t:20,val:'0'}]},{id:'print-bus',name:'bus',type:'multi',color:'#ff0000',radix:'hex',data:[{t:0,val:'x'},{t:20,val:'0'}]}];
  state.texts=[];state.measurements=[];state.connections=[];state.selectedIds.clear();state.mode='VIEW';state.subMode='NORMAL';state.hoverEdgeT=null;editorSelection=null;measurementCursors=[];state.offsetX=state.offsetY=0;state.scaleX=10;
  if(!state.printMode)togglePrintMode();updateUI();render();
  const pixels=ctx.getImageData(0,0,canvas.width,canvas.height).data;
  let coloured=0;for(let i=0;i<pixels.length;i+=4)if(pixels[i]!==pixels[i+1]||pixels[i+1]!==pixels[i+2])coloured++;
  return coloured;
 });assert.equal(printPixels,0);console.log('Binary and bus X-state print rendering is entirely grayscale PASS');
 // Verify explicit drawing colours without a global CSS colour conversion.
 assert.equal(await page.locator('#waveCanvas').evaluate(el=>getComputedStyle(el).filter),'none');
 assert.deepEqual(await page.evaluate(()=>{const t=getTheme();return [t.getSigColor('#ff0000'),t.xState,t.xHatch,t.zState];}),['#000000','#888888','#888888','#888888']);
 const monochromeScreenshot=PNG.sync.read(await page.locator('#waveCanvas').screenshot());
 let colouredDisplayPixels=0;
 for(let i=0;i<monochromeScreenshot.data.length;i+=4) {
  const p=monochromeScreenshot.data;if(p[i]!==p[i+1] || p[i+1]!==p[i+2])colouredDisplayPixels++;
 }
 assert.equal(colouredDisplayPixels,0);
 await page.evaluate(()=>{togglePrintMode();render();});
 const colourScreenshot=PNG.sync.read(await page.locator('#waveCanvas').screenshot());
 let redPixels=0;
 for(let i=0;i<colourScreenshot.data.length;i+=4)if(colourScreenshot.data[i]>colourScreenshot.data[i+1]+20)redPixels++;
 assert(redPixels>0);
 console.log('Explicit print palette: ordinary signals black, X/Z gray, no grayscale filter PASS');

 assert.equal(errors.length,0,errors.join('\n'));console.log('browser errors: 0');
} finally {await browser.close();await new Promise(r=>server.close(r));}
})();
