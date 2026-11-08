"""Design, verify, export and plot the FIR example used by the notes."""
from pathlib import Path
import json
import os
os.environ.setdefault('MPLCONFIGDIR','/tmp/ic-notes-mpl')
import numpy as np
from scipy.signal import kaiserord, firwin, freqz
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'docs/img/fir_design'
FS=100_000_000.
FP, FSTOP=10_000_000.,15_000_000.
RP, AS=.1,60.
GRID=131073
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,
 'axes.spines.top':False,'axes.spines.right':False,'svg.fonttype':'path','svg.hashsalt':'fir-design'})


def response(h):
    return freqz(h,worN=GRID,fs=FS,include_nyquist=True)


def measure(h, highpass=False):
    f,H=response(h);a=np.abs(H)
    pb=a[f>=FSTOP] if highpass else a[f<=FP]
    sb=a[f<=FP] if highpass else a[f>=FSTOP]
    return dict(passband_ripple_db=float(20*np.log10(pb.max()/pb.min())),
                stopband_attenuation_db=float(-20*np.log10(sb.max())),
                dc_gain=float(np.sum(h)))


def design(highpass=False):
    delta_p=(10**(RP/20)-1)/(10**(RP/20)+1)
    delta_s=10**(-AS/20)
    attenuation=-20*np.log10(min(delta_p,delta_s))
    n,beta=kaiserord(attenuation,(FSTOP-FP)/(FS/2))
    initial=int(n)
    if n%2==0:n+=1
    for _ in range(100):
        h=firwin(n,(FP+FSTOP)/2,window=('kaiser',beta),fs=FS,pass_zero=not highpass)
        result=measure(h,highpass)
        if result['passband_ripple_db']<=RP and result['stopband_attenuation_db']>=AS:
            return h,beta,initial,result
        n+=2
    raise RuntimeError('Tap search did not meet specifications')


def save(fig,name):
    path=OUT/name
    fig.savefig(path,bbox_inches='tight',facecolor='white',metadata={'Date':None});plt.close(fig)
    path.write_text('\n'.join(l.rstrip() for l in path.read_text().splitlines())+'\n')


def db(H):return 20*np.log10(np.maximum(np.abs(H),1e-8))


def plots(h,beta):
    f,H=response([.25,.5,.25]);_,HP=response([-.25,.5,-.25]);u=f/FS
    assert np.allclose(abs(H),np.cos(np.pi*u)**2,atol=1e-12)
    assert np.allclose(abs(HP),np.sin(np.pi*u)**2,atol=1e-12)
    fig,ax=plt.subplots(figsize=(8,3.6),constrained_layout=True)
    ax.plot(u,abs(H),'k',label='Low-pass: [1, 2, 1] / 4')
    ax.plot(u,abs(HP),'k--',label='High-pass: [-1, 2, -1] / 4')
    ax.set(xlabel='Frequency f / fs',ylabel='Magnitude',xlim=(0,.5),ylim=(-.03,1.08),title='The coefficients determine which frequencies pass')
    ax.legend(fontsize=9);ax.grid(alpha=.2);save(fig,'low_high_response.svg')

    f,H=response(h)
    fig,axes=plt.subplots(2,1,figsize=(8,5.5),constrained_layout=True)
    axes[0].plot(f/1e6,db(H),'k');axes[0].axhline(-AS,color='.5',ls='--')
    axes[0].axvspan(0,FP/1e6,color='.94');axes[0].axvspan(FP/1e6,FSTOP/1e6,color='.84')
    axes[0].set(xlabel='Frequency (MHz)',ylabel='Magnitude (dB)',ylim=(-110,2),xlim=(0,FS/2/1e6),title=f'{len(h)} taps: passband 0–10 MHz, stopband 15–50 MHz')
    axes[0].text(24,-57,'Stopband target: −60 dB',fontsize=10)
    axes[1].plot(f/1e6,db(H),'k');axes[1].set(xlabel='Frequency (MHz)',ylabel='Magnitude (dB)',xlim=(0,10),ylim=(-.055,.055),title='Passband detail: ripple is small but not zero')
    for ax in axes:ax.grid(alpha=.18)
    save(fig,'design_specification.svg')

    fig,ax=plt.subplots(figsize=(8,3.7),constrained_layout=True)
    for n,style in [(17,':'),(33,'--'),(len(h),'-')]:
        taps=firwin(n,(FP+FSTOP)/2,window=('kaiser',beta),fs=FS)
        f,H=response(taps);ax.plot(f/1e6,db(H),color='k',ls=style,lw=1.2,label=f'{n} taps')
    ax.axvspan(10,15,color='.9');ax.axhline(-60,color='.6',lw=.8)
    ax.set(xlabel='Frequency (MHz)',ylabel='Magnitude (dB)',xlim=(0,30),ylim=(-100,2),title='Same cutoff and Kaiser beta; different tap counts')
    ax.legend();ax.grid(alpha=.18);save(fig,'tap_tradeoff.svg')

    fig,ax=plt.subplots(figsize=(8,3.7),constrained_layout=True)
    for label,taps,style in [('Float coefficients',h,'-'),('16-bit / 15 fractional bits',np.rint(h*2**15)/2**15,'--'),('12-bit / 11 fractional bits',np.rint(h*2**11)/2**11,':')]:
        f,H=response(taps);ax.plot(f/1e6,db(H),color='k',ls=style,lw=1.1,label=label)
    ax.axhline(-60,color='.5',lw=.8)
    ax.set(xlabel='Frequency (MHz)',ylabel='Magnitude (dB)',xlim=(15,50),ylim=(-100,-45),title='Coefficient quantization changes the stopband')
    ax.legend(fontsize=9);ax.grid(alpha=.18);save(fig,'coefficient_quantization.svg')


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    h,beta,initial,result=design();n=len(h)
    integers=np.rint(h*2**15).astype(np.int64)
    assert np.array_equal(integers,integers[::-1])
    assert integers.min()>=-32768 and integers.max()<=32767
    qmetrics={}
    for bits in [12,16,20]:qmetrics[str(bits)]=measure(np.rint(h*2**(bits-1))/2**(bits-1))
    bound=32768*sum(abs(int(v)) for v in integers)
    acc_bits=1+bound.bit_length()
    report=dict(sample_rate_hz=FS,passband_edge_hz=FP,stopband_edge_hz=FSTOP,
        ripple_target_db=RP,attenuation_target_db=AS,cutoff_hz=(FP+FSTOP)/2,
        kaiser_initial_numtaps=initial,numtaps=n,order=n-1,beta=float(beta),
        group_delay_samples=(n-1)/2,group_delay_seconds=(n-1)/(2*FS),
        measured=result,quantized=qmetrics,frequency_grid_points=GRID,
        accumulator_bits_generic=16+16+int(np.ceil(np.log2(n))),
        accumulator_bits_for_this_coefficient_set=acc_bits,
        measurement='Dense frequency-grid check, not an analytic all-frequency bound')
    (OUT/'design_report.json').write_text(json.dumps(report,indent=2)+'\n')
    np.savetxt(OUT/'coefficients.csv',np.column_stack([np.arange(n),h,integers,integers/2**15]),delimiter=',',
        header='tap,float_coefficient,q1_15_integer,reconstructed_coefficient',comments='',fmt=['%d','%.18g','%d','%.18g'])
    hp,hp_beta,_,hp_result=design(highpass=True)
    report['highpass_example']=dict(numtaps=len(hp),beta=float(hp_beta),measured=hp_result,
        stopband_edge_hz=FP,passband_edge_hz=FSTOP,
        initial_75_tap_measurement=measure(firwin(75,(FP+FSTOP)/2,fs=FS,window=('kaiser',beta),pass_zero=False),True))
    (OUT/'design_report.json').write_text(json.dumps(report,indent=2)+'\n')
    np.savetxt(OUT/'highpass_coefficients.csv',np.column_stack([np.arange(len(hp)),hp]),
        delimiter=',',header='tap,float_coefficient',comments='',fmt=['%d','%.18g'])
    plots(h,beta)
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
