const {chromium}=require('playwright');
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
 await page.locator('#clockModal button[type="submit"]').click();
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
 await page.locator('#clockPeriod').fill('0');await page.locator('#clockModal button[type="submit"]').click();
 assert.equal(await page.evaluate(()=>state.tree.length),0);assert(await page.locator('#clockError').textContent());
 await page.locator('#clockPeriod').fill('10');await page.locator('#clockStart').fill('0');await page.locator('#clockCount').fill('1');
 await page.locator('#clockModal button[type="submit"]').click();
 assert.equal(await page.evaluate(()=>state.tree.length),1);assert.equal(await page.evaluate(()=>state.tree[0].type),'single');
 assert.equal(await page.evaluate(()=>state.tree[0].data.at(-1).t),10);
 console.log('Empty project clock creation and invalid parameter protection PASS');
 for (const [unit, value, expected] of [['ps','500',0.5],['ns','2',2],['us','0.25',250],['ms','0.001',1000]]) {
  const previousCount=await page.evaluate(()=>state.tree.length);
  await page.getByTitle('添加信号',{exact:true}).hover();await page.locator('#addClockButton').click();
  await page.locator('#clockPeriod').fill(value);await page.locator('#clockPeriodUnit').selectOption(unit);
  await page.locator('#clockStart').fill('1000');await page.locator('#clockStartUnit').selectOption('ps');
  await page.locator('#clockCount').fill('2');await page.locator('#clockModal button[type="submit"]').click();
  assert.equal(await page.evaluate(()=>state.tree.length),previousCount+1);
  assert.equal(await page.evaluate(()=>state.tree.at(-1).data.at(-1).t),1+2*expected);
 }
 assert.equal(await page.evaluate(()=>new Set(state.tree.map(s=>s.id)).size),await page.evaluate(()=>state.tree.length));
 console.log('Numeric time inputs, ps/ns/us/ms conversion and creation without crypto.randomUUID PASS');

 assert.equal(errors.length,0,errors.join('\n'));console.log('browser errors: 0');
} finally {await browser.close();await new Promise(r=>server.close(r));}
})();
