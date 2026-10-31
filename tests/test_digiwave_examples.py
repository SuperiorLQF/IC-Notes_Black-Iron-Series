"""Protocol checks for the educational waveforms; no external dependencies."""
import json
import unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]/'docs'/'digiwave'

def load(name):
    p=json.loads((ROOT/'examples'/f'{name}.json').read_text())
    signals={}
    def visit(nodes):
        for n in nodes:
            if n['type']=='group': visit(n['children'])
            else: signals[n['name']]=n
    visit(p['tree'])
    return p,signals

def value(sig,t):
    result=sig['data'][0]['val']
    for event in sig['data']:
        if event['t']>t+1e-7: break
        result=event['val']
    return result

def number(sig,t): return int(value(sig,t),0) if value(sig,t).startswith('0x') else int(value(sig,t))
def rises(sig): return [e['t'] for e in sig['data'] if e['val']=='1']
def transfers(s,prefix): return [t for t in rises(s['clk']) if value(s[prefix+'VALID'],t)=='1' and value(s[prefix+'READY'],t)=='1']

class ProtocolExamples(unittest.TestCase):
    def test_catalog_and_json_match(self):
        entries=json.loads((ROOT/'examples.js').read_text().split(' = ',1)[1].strip().removesuffix(';'))
        self.assertEqual(len(entries),6)
        for entry in entries:
            data,_=load(entry['id']);data.pop('example')
            self.assertEqual(data,entry['project'])
    def check_stability(self,s,prefix,payload):
        edges=rises(s['clk'])
        for before,after in zip(edges,edges[1:]):
            if value(s[prefix+'VALID'],before)=='1' and value(s[prefix+'READY'],before)=='0':
                self.assertEqual(value(s[prefix+'VALID'],after),'1')
                for name in payload: self.assertEqual(value(s[name],before),value(s[name],after),name)
    def test_axi_lite(self):
        p,s=load('axi4-lite')
        for channel,expected in [('AW',[35]),('W',[25]),('B',[75]),('AR',[105]),('R',[155])]: self.assertEqual(transfers(s,channel),expected)
        self.assertEqual(number(s['WDATA'],25),0xDEADBEEF);self.assertEqual(number(s['RDATA'],155),0xDEADBEEF)
        self.assertEqual(number(s['AWADDR'],35),number(s['ARADDR'],105))
        self.assertGreater(len(p['texts']),3)
        for prefix,payload in [('AW',['AWADDR']),('W',['WDATA','WSTRB']),('R',['RDATA','RRESP']),('B',['BRESP'])]: self.check_stability(s,prefix,payload)
    def test_axi_burst(self):
        _,s=load('axi4-burst')
        self.assertEqual(transfers(s,'W'),[45,55,75,85]);self.assertEqual(transfers(s,'R'),[195,205,225,235])
        self.assertEqual([number(s['WDATA'],t) for t in transfers(s,'W')],[0x11111111,0x22222222,0x33333333,0x44444444])
        self.assertEqual([number(s['RDATA'],t) for t in transfers(s,'R')],[0x11111111,0x22222222,0x33333333,0x44444444])
        for prefix,t in [('AW',35),('AR',155)]:
            self.assertEqual(number(s[prefix+'LEN'],t),3);self.assertEqual(number(s[prefix+'SIZE'],t),2);self.assertEqual(number(s[prefix+'BURST'],t),1)
        self.assertEqual([value(s['WLAST'],t) for t in transfers(s,'W')],['0','0','0','1'])
        self.assertEqual([value(s['RLAST'],t) for t in transfers(s,'R')],['0','0','0','1'])
        self.assertEqual(number(s['BID'],125),number(s['AWID'],35));self.assertEqual(number(s['RID'],195),number(s['ARID'],155))
        self.check_stability(s,'W',['WDATA','WSTRB','WLAST']);self.check_stability(s,'R',['RDATA','RID','RRESP','RLAST'])
    def test_axi_stream(self):
        _,s=load('axi-stream');t=transfers(s,'T')
        self.assertEqual(t,[35,45,75,85]);self.assertEqual([value(s['TLAST'],x) for x in t],['0','0','0','1'])
        self.assertEqual([number(s['TKEEP'],x) for x in t],[15,15,15,3]);self.check_stability(s,'T',['TDATA','TKEEP','TLAST'])
    def test_apb(self):
        _,s=load('apb');done=[t for t in rises(s['clk']) if all(value(s[n],t)=='1' for n in ['PSEL','PENABLE','PREADY'])]
        self.assertEqual(done,[65,95]);self.assertEqual(value(s['PWRITE'],65),'1');self.assertEqual(value(s['PWRITE'],95),'0')
        for t in [35,45,55,65]: self.assertEqual(number(s['PADDR'],t),0x20);self.assertEqual(number(s['PWDATA'],t),0x12345678)
    def test_spi_mode0(self):
        _,s=load('spi-mode0');sample=rises(s['SCLK']);self.assertEqual(len(sample),8)
        for name,expected in [('MOSI',0xA5),('MISO',0x3C)]: self.assertEqual(int(''.join(value(s[name],t) for t in sample),2),expected)
        self.assertTrue(all(value(s['CS_n'],t)=='0' for t in sample));self.assertEqual(value(s['SCLK'],0),'0')
    def test_uart(self):
        _,s=load('uart-8n1');bit=1e9/115200
        for start,expected in [(20000,0x55),(20000+12*bit,0xA3)]:
            self.assertEqual(value(s['TX'],start+bit*.5),'0')
            byte=sum(int(value(s['TX'],start+(i+1.5)*bit))<<i for i in range(8))
            self.assertEqual(byte,expected);self.assertEqual(value(s['TX'],start+9.5*bit),'1')

if __name__=='__main__': unittest.main()
