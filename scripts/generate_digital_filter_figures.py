"""Reproducible vector diagrams and computed waveforms for digital filter notes."""
from pathlib import Path
from html import escape
import os
os.environ.setdefault('MPLCONFIGDIR', '/tmp/ic-notes-mpl')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parents[1]/'docs/img/digital_filters'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'svg.fonttype':'path','svg.hashsalt':'ic-digital-filters'})


def save(fig, name):
    fig.savefig(OUT/name, bbox_inches='tight', facecolor='white', metadata={'Date':None})
    plt.close(fig)


def stems(ax, n, values, title):
    marker, lines, base = ax.stem(n, values, linefmt='k-', markerfmt='ko', basefmt='k-')
    marker.set_markersize(5);lines.set_linewidth(1.5);base.set_linewidth(.7)
    ax.set(title=title, xlabel='Sample index n', ylabel='Amplitude')
    ax.grid(axis='y', alpha=.18)


def waveforms():
    fig, axes=plt.subplots(2,1,figsize=(8,4.4),constrained_layout=True)
    x=np.array([0.,0,9,0,0,0]);y=np.convolve(x,np.ones(3)/3)[:6]
    assert np.array_equal(y,[0,0,3,3,3,0])
    for ax,a,title in zip(axes,[x,y],['Input: one pulse','Output: three-point moving average']):
        stems(ax,np.arange(6),a,title);ax.set_xticks(range(6));ax.set_ylim(-.5,10)
    save(fig,'moving_average.svg')

    n=np.arange(13);fir=np.r_[.25,.5,.25,np.zeros(10)];iir=.5**(n+1)
    assert np.allclose(iir[1:],.5*iir[:-1])
    fig,axes=plt.subplots(2,1,figsize=(8,4.4),constrained_layout=True)
    for ax,a,title in zip(axes,[fir,iir],['FIR: h = [1, 2, 1] / 4','IIR: y[n] = 0.5 x[n] + 0.5 y[n-1]']):
        stems(ax,n,a,title);ax.set_xticks(range(0,13,2));ax.set_ylim(-.03,.56)
    save(fig,'impulse_comparison.svg')

    x=np.array([1.,2,0,-1]);u=np.zeros(2*len(x)-1);u[::2]=x
    # Gain-2 triangular interpolation filter. Crop only after compensating its
    # one-high-rate-sample group delay; the figure displays this aligned interval.
    v=np.convolve(u,[.5,1,.5])[1:1+len(u)]
    assert np.allclose(v[::2],x)
    fig,axes=plt.subplots(3,1,figsize=(8,6),constrained_layout=True)
    for ax,idx,a,title in zip(axes,[np.arange(4),np.arange(7)/2,np.arange(7)/2],[x,u,v],
        ['Original samples','Upsample by 2: insert zeros','Filter with [0.5, 1, 0.5]: delay compensated']):
        stems(ax,idx,a,title);ax.set_xlabel('Time / original sample period');ax.set_xticks(np.arange(0,3.5,.5));ax.set_ylim(-1.4,2.4)
    save(fig,'interpolation.svg')

    t=np.linspace(0,.08,1500);ts=np.arange(9)/100
    hi=np.cos(2*np.pi*70*ts);lo=np.cos(2*np.pi*30*ts)
    assert np.allclose(hi,lo,atol=1e-12)
    fig,ax=plt.subplots(figsize=(8,3.2),constrained_layout=True)
    ax.plot(t*1000,np.cos(2*np.pi*70*t),color='.65',lw=1,label='70 MHz component')
    ax.plot(t*1000,np.cos(2*np.pi*30*t),'k--',lw=1.2,label='30 MHz alias')
    ax.plot(ts*1000,hi,'ko',label='Samples at 100 Msps',ms=5)
    # 100 in these numeric coordinates is MHz; time is in microseconds.
    ax.set(xlabel='Time (ns)',ylabel='Amplitude',title='After 2:1 downsampling: 70 MHz aliases to 30 MHz')
    ax.legend(loc='upper right',fontsize=8,ncol=3);ax.grid(alpha=.15)
    save(fig,'aliasing.svg')


def svg_start(width,height,title):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="{escape(title)}">',
      '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="#111"/></marker></defs>',
      f'<rect width="{width}" height="{height}" fill="white"/>']


def line(s,points,arrow=False):
    s.append(f'<path d="{points}" fill="none" stroke="#111" stroke-width="2"'+(' marker-end="url(#arrow)"' if arrow else '')+'/>')


def text(s,x,y,label,size=18,anchor='middle'):
    s.append(f'<text x="{x}" y="{y}" fill="#111" font-family="DejaVu Sans,Arial,sans-serif" font-size="{size}" text-anchor="{anchor}">{escape(label)}</text>')


def box(s,x,y,w,h,label):
    s.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="white" stroke="#111" stroke-width="2" rx="3"/>')
    text(s,x+w/2,y+h/2+6,label)


def dot(s,x,y):s.append(f'<circle cx="{x}" cy="{y}" r="3.5" fill="#111"/>')


def finish(s,name):
    (OUT/name).write_text('\n'.join(s+['</svg>'])+'\n')


def diagrams():
    s=svg_start(720,310,'3-tap FIR direct form')
    text(s,45,65,'x[n]');line(s,'M45 90H180',True)
    box(s,180,67,70,46,'z⁻¹');line(s,'M250 90H390',True)
    box(s,390,67,70,46,'z⁻¹');line(s,'M460 90H545')
    for x,label,weight in [(105,'x[n]','× 0.25'),(315,'x[n−1]','× 0.5'),(525,'x[n−2]','× 0.25')]:
        dot(s,x,90);line(s,f'M{x} 90V155',True);box(s,x-48,155,96,44,weight)
        text(s,x,135,label,14);line(s,f'M{x} 199V{240 if x==105 else 220}',x!=105)
    # Two explicit adders, not a bus joining distinct signal outputs.
    line(s,'M105 240H295',True)
    for cx in (315,525):
        s.append(f'<circle cx="{cx}" cy="240" r="20" fill="white" stroke="#111" stroke-width="2"/>')
        text(s,cx,247,'Σ',24)
    line(s,'M335 240H505',True)
    line(s,'M545 240H702',True);text(s,676,219,'y[n]')
    text(s,360,292,'z⁻¹ = one valid-sample delay',16)
    finish(s,'fir_structure.svg')

    s=svg_start(720,285,'First-order IIR with output feedback')
    text(s,40,65,'x[n]');line(s,'M40 90H125',True);box(s,125,67,100,46,'× 0.5');line(s,'M225 90H338',True)
    s.append('<circle cx="360" cy="90" r="21" fill="white" stroke="#111" stroke-width="2"/>');text(s,360,97,'Σ',24)
    line(s,'M381 90H680',True);text(s,653,65,'y[n]');dot(s,570,90)
    line(s,'M570 90V210H505',True);box(s,425,187,80,46,'z⁻¹');line(s,'M425 210H325',True)
    box(s,225,187,100,46,'× 0.5');line(s,'M225 210H160V140H360V112',True)
    text(s,365,245,'y[n−1]',16);text(s,360,275,'Feedback keeps past output in the state',16)
    finish(s,'iir_structure.svg')

    s=svg_start(760,350,'Interpolation, decimation and rational sample rate conversion')
    # Arrows denote sample-stream flow; FIR gain for interpolation is L.
    for y,label,blocks in [
      (65,'Interpolation',[(170,'↑ L'),(365,'LPF (gain L)')]),
      (170,'Decimation',[(170,'Anti-alias LPF'),(425,'↓ M')]),
      (275,'Rational L/M',[(145,'↑ L'),(315,'LPF (gain L)'),(525,'↓ M')])]:
        text(s,20,y-30,label,17,'start');prev=25
        for x,b in blocks:
            width=155 if 'LPF' in b else 95
            line(s,f'M{prev} {y}H{x}',True);box(s,x,y-22,width,44,b);prev=x+width
        line(s,f'M{prev} {y}H735',True)
    text(s,380,338,'Example: 100 Msps → ↑3 → LPF → ↓2 → 150 Msps',17)
    finish(s,'rate_conversion.svg')

    s=svg_start(760,255,'Clock cycles and valid samples')
    x0,step=150,60
    text(s,20,40,'Clock cycle',17,'start')
    text(s,20,105,'sample_vld',17,'start')
    text(s,20,170,'Data',17,'start')
    for i in range(10):text(s,x0+i*step,40,str(i),15)
    path=f'M{x0-step/2} 120'
    for i in range(10):
        left=x0+i*step-step/2;level=85 if i%4==0 else 120
        path+=f'H{left}V{level}H{left+step}'
    path+='V120';line(s,path)
    for i in [0,4,8]:
        x=x0+i*step;line(s,f'M{x} 132V148',True);text(s,x,175,f'x[{i//4}]',17)
    text(s,380,225,'249.6 MHz clock / 4 cycles per sample = 62.4 Msps',17)
    finish(s,'valid_sample_timing.svg')


if __name__=='__main__':
    OUT.mkdir(parents=True,exist_ok=True)
    waveforms();diagrams()
    print('Generated 8 checked SVG figures in',OUT)
