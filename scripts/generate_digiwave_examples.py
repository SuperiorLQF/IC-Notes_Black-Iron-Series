"""Generate the built-in editable protocol examples and standalone JSON projects."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1] / 'docs' / 'digiwave'
PALETTE = ['#70f5ff', '#ffe66d', '#ff80bd', '#87e6a1', '#b5a1ff', '#ffba78']

def signal(name, events, bus=False, anchors=()):
    data=[]
    for t,v in sorted(events, key=lambda e:e[0]):
        event={'t':round(t,6),'val':str(v)}
        if data and data[-1]['t']==event['t']: data[-1]=event
        elif not data or data[-1]['val']!=event['val']: data.append(event)
    out={'id':name,'name':name,'type':'multi' if bus else 'single','color':PALETTE[len(name)%len(PALETTE)],'thickness':2,'data':data}
    if anchors: out['anchors']=sorted(set(round(t,6) for t in anchors))
    return out

def binary(name, *intervals, idle='0', anchors=()):
    events=[(0,idle)]
    for a,b in intervals: events.extend([(a,'1' if idle=='0' else '0'),(b,idle)])
    return signal(name,events,anchors=anchors)

def bus(name, *intervals):
    events=[(0,'0')]
    for a,b,value in intervals: events.extend([(a,value),(b,'0')])
    return signal(name,events,True)

def clock(end):
    return signal('clk',[(0,'0')]+[(t,'1' if t%10==5 else '0') for t in range(5,end+1,5)])

def group(name,children,expanded=True):
    return {'id':'group_'+name,'name':name,'type':'group','expanded':expanded,'children':children}

def note(track,t,title,content):
    return {'id':f'note_{track}_{t}','trackId':track,'t':t,'y':42,'text':title,'content':content,'size':13,'color':'#ffe66d','bgColor':'#252b35','isSticky':True,'collapsed':True,'baseScale':10}

def arrow(name,s1,t1,s2,t2):
    return {'id':name,'sigId1':s1,'t1':t1,'sigId2':s2,'t2':t2,'text':'','color':'#ffba78','thickness':1}

def project(tree,texts,connections=()):
    return {'formatVersion':1,'tree':tree,'texts':texts,'measurements':[],'connections':list(connections),'scaleX':10}

def common(end):
    return group('Clock & Reset',[clock(end),signal('resetn',[(0,'0'),(10,'1')])])

examples=[]
def add(key,title,description,data):
    examples.append({'id':key,'title':title,'description':description,'project':data})

add('axi4-lite','AXI4-Lite · Write + Read','独立 AW/W 握手、延迟响应；写后读回同一寄存器，带 transaction 注释。',project([
 common(180),
 group('Write address',[binary('AWVALID',(20,40),anchors=[35]),binary('AWREADY',(30,40)),bus('AWADDR',(20,40,'0x40000010')),bus('AWPROT',(20,40,'0'))]),
 group('Write data',[binary('WVALID',(10,30),anchors=[25]),binary('WREADY',(20,30)),bus('WDATA',(10,30,'0xDEADBEEF')),bus('WSTRB',(10,30,'0xF'))]),
 group('Write response',[binary('BVALID',(50,80),anchors=[75]),binary('BREADY',(70,80)),bus('BRESP',(50,80,'0'))]),
 group('Read address',[binary('ARVALID',(90,110),anchors=[105]),binary('ARREADY',(100,110)),bus('ARADDR',(90,110,'0x40000010')),bus('ARPROT',(90,110,'0'))],False),
 group('Read data',[binary('RVALID',(130,160),anchors=[155]),binary('RREADY',(150,160)),bus('RDATA',(130,160,'0xDEADBEEF')),bus('RRESP',(130,160,'0'))],False)
],[
 note('clk',15,'AXI4-Lite: WRITE #1 / READ #2','所有传输在 clk 上升沿且 VALID && READY 时发生。展开或滚动各通道组查看事务。'),
 note('AWADDR',20,'WRITE #1: [0x40000010] ← 0xDEADBEEF','W 握手 25ns，AW 握手 35ns：写数据可先于地址到达。WSTRB=0xF，4 个字节有效。'),
 note('BVALID',50,'WRITE #1 response: OKAY @75ns','BVALID 从 50ns 保持到 BREADY；75ns 完成写响应。'),
 note('ARADDR',90,'READ #2: [0x40000010]','105ns 接收读地址。'),
 note('RDATA',130,'READ #2: 0xDEADBEEF / OKAY @155ns','RVALID 期间数据保持稳定；RREADY 延迟至 150ns，155ns 完成读返回。')
],[arrow('write_addr_to_response','AWVALID',35,'BVALID',75),arrow('write_data_to_response','WVALID',25,'BVALID',75),arrow('read_transaction','ARVALID',105,'RVALID',155)]))

add('axi4-burst','AXI4 · 4-beat INCR Burst','32-bit 数据，四拍写入与读回；展示 LEN/SIZE/BURST/ID、LAST 和中途背压。',project([
 common(260),
 group('Write address',[binary('AWVALID',(20,40),anchors=[35]),binary('AWREADY',(30,40)),bus('AWADDR',(20,40,'0x80000000')),bus('AWID',(20,40,'3')),bus('AWLEN',(20,40,'3')),bus('AWSIZE',(20,40,'2')),bus('AWBURST',(20,40,'1'))]),
 group('Write burst data',[binary('WVALID',(30,90),anchors=[45,55,75,85]),binary('WREADY',(40,60),(70,90)),bus('WDATA',(30,50,'0x11111111'),(50,60,'0x22222222'),(60,80,'0x33333333'),(80,90,'0x44444444')),bus('WSTRB',(30,90,'0xF')),binary('WLAST',(80,90))]),
 group('Write response',[binary('BVALID',(100,130),anchors=[125]),binary('BREADY',(120,130)),bus('BID',(100,130,'3')),bus('BRESP',(100,130,'0'))]),
 group('Read address',[binary('ARVALID',(140,160),anchors=[155]),binary('ARREADY',(150,160)),bus('ARADDR',(140,160,'0x80000000')),bus('ARID',(140,160,'5')),bus('ARLEN',(140,160,'3')),bus('ARSIZE',(140,160,'2')),bus('ARBURST',(140,160,'1'))],False),
 group('Read burst data',[binary('RVALID',(180,240),anchors=[195,205,225,235]),binary('RREADY',(190,210),(220,240)),bus('RDATA',(180,200,'0x11111111'),(200,210,'0x22222222'),(210,230,'0x33333333'),(230,240,'0x44444444')),bus('RID',(180,240,'5')),bus('RRESP',(180,240,'0')),binary('RLAST',(230,240))],False)
],[
 note('AWADDR',20,'WRITE burst #1: 4 × 32-bit INCR','AWLEN=3 表示 4 拍；AWSIZE=2 表示每拍 4 字节；AWBURST=1 表示 INCR。AWID=3。地址依次为 0x80000000/04/08/0C。'),
 note('WDATA',30,'W beats @45 / 55 / 75 / 85ns','第 3 拍在 65ns 遇到背压，数据保持至 75ns 握手。WLAST 只在最后一拍为 1。'),
 note('BVALID',100,'WRITE burst #1: OKAY @125ns','BID=3，与 AWID 对应。写响应晚于四拍数据完成。'),
 note('ARADDR',140,'READ burst #2: ID=5 / 4 beats','155ns 握手读地址。单 outstanding transaction 示例，不演示乱序返回。'),
 note('RDATA',180,'R beats @195 / 205 / 225 / 235ns','215ns 为背压等待；RID=5，RRESP=OKAY，RLAST 只标记第 4 拍。')
],[arrow('burst_write','AWVALID',35,'BVALID',125),arrow('burst_read','ARVALID',155,'RVALID',235)]))

add('axi-stream','AXI-Stream · Packet + Backpressure','四拍数据包，VALID/READY 背压，最后一拍 TLAST=1 且 TKEEP=0x3。',project([
 common(110),group('AXI Stream',[
 binary('TVALID',(20,90),anchors=[35,45,75,85]),binary('TREADY',(30,50),(70,90)),
 bus('TDATA',(20,40,'0x11223344'),(40,50,'0x55667788'),(50,80,'0x99AABBCC'),(80,90,'0x0000DDEE')),
 bus('TKEEP',(20,80,'0xF'),(80,90,'0x3')),binary('TLAST',(80,90))])
],[note('TDATA',20,'Packet #1: 4 beats / 14 valid bytes','握手时刻 35、45、75、85ns。最后一拍仅低两字节有效，TLAST 在最后一拍为 1。'),note('TVALID',50,'Backpressure: hold beat #3','55ns、65ns 时 TVALID=1、TREADY=0；TDATA/TKEEP/TLAST 均必须保持，直到 75ns 握手。')]))

add('apb','APB · Write / Wait / Read','Setup → Access → Wait → Complete，展示 PREADY 等待与寄存器读写。',project([
 common(120),group('APB',[
 binary('PSEL',(20,70),(80,100)),binary('PENABLE',(30,70),(90,100),anchors=[35,45,55,65,95]),binary('PWRITE',(20,70)),
 signal('PREADY',[(0,'1'),(20,'0'),(60,'1')]),bus('PADDR',(20,70,'0x20'),(80,100,'0x20')),bus('PWDATA',(20,70,'0x12345678')),bus('PRDATA',(90,100,'0x12345678')),binary('PSLVERR')])
],[note('PADDR',20,'WRITE #1: [0x20] ← 0x12345678','25ns 是 Setup 阶段；35/45/55ns 处于 Access 等待，65ns PSEL && PENABLE && PREADY 为 1，写完成。'),note('PENABLE',30,'Wait states: PREADY=0','等待期间地址、写使能和写数据保持不变。'),note('PRDATA',90,'READ #2 completed @95ns','85ns Setup，95ns Access 完成；PRDATA=0x12345678，PSLVERR=0。')]))

spi_end=220
sclk=[(0,'0')]
for i in range(8): sclk += [(30+20*i,'1'),(40+20*i,'0')]
def spi_bits(name,value):
    return signal(name,[(0,'0')]+[(20 if i==0 else 20+20*i,str((value>>(7-i))&1)) for i in range(8)]+[(200,'0')],anchors=[30+20*i for i in range(8)])
add('spi-mode0','SPI Mode 0 · Full Duplex','CPOL=0 / CPHA=0，MSB first，MOSI=0xA5、MISO=0x3C。',project([
 group('SPI',[binary('CS_n',(20,200),idle='1',anchors=[220]),signal('SCLK',sclk),spi_bits('MOSI',0xA5),spi_bits('MISO',0x3C)])
],[note('CS_n',20,'SPI transaction #1: 8 bits','CS_n 拉低后开始；SCLK 空闲为低，接收端在上升沿采样，发送端在下降沿切换下一位。'),note('MOSI',30,'TX 0xA5: 10100101','MSB first。采样点为 30、50、70、90、110、130、150、170ns。'),note('MISO',30,'RX 0x3C: 00111100','与 MOSI 同时传输，200ns CS_n 拉高结束事务。')]))

bit_ns=1e9/115200
uart_events=[(0,'1')]
starts=[20000,20000+12*bit_ns]
notes=[]
for i,(start,value) in enumerate(zip(starts,[0x55,0xA3])):
    uart_events.append((start,'0'))
    uart_events.extend((start+(j+1)*bit_ns,str((value>>j)&1)) for j in range(8))
    uart_events.append((start+9*bit_ns,'1'))
    notes.append(note('TX',round(start,6),f'UART frame #{i+1}: 0x{value:02X}',f'115200 baud，8N1，LSB first。起始位 0，8 位数据，无校验，1 位停止位 1。每位约 {bit_ns:.3f}ns。'))
add('uart-8n1','UART · 115200 / 8N1','两帧 0x55、0xA3；起始位、LSB-first 数据、停止位和帧间空闲。',project([
 group('UART',[signal('TX',uart_events,anchors=[round(start+j*bit_ns,6) for start in starts for j in range(11)]),signal('RX_idle',[(0,'1')])])
],notes))

if __name__=='__main__':
    folder=ROOT/'examples';folder.mkdir(exist_ok=True)
    for example in examples:
        data={**example['project'],'example':{'title':example['title'],'description':example['description']}}
        (folder/(example['id']+'.json')).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
    (ROOT/'examples.js').write_text('// Generated by scripts/generate_digiwave_examples.py; times are in ns.\nwindow.DIGIWAVE_EXAMPLES = '+json.dumps(examples,ensure_ascii=False,separators=(',',':'))+';\n')
    print(f'Generated {len(examples)} editable protocol examples')
