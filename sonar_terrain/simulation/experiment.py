"""Small simulated sonar acquisition environment and tabular Q-learning benchmark.

No GPU, pretrained models or extra runtime dependencies. Rewards use simulator
truth during training only; policy actions depend solely on sampled locations.
"""
from __future__ import annotations
import argparse
import json
import sys
import time
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from reconstruct import forward, reconstruct


class SonarEnv:
    """Select a cross-track ping row in a static 12 x 48 simulated swath.

    Actions are survey locations, not vessel dynamics. Observations contain only
    acquired returns and their mask. Truth is reserved for reward/scoring.
    """
    rows, cols = 12, 48

    def __init__(self, seed, budget=4, mismatch=False):
        if not 1 <= budget <= self.rows:
            raise ValueError('budget must be between 1 and 12')
        self.budget = budget
        rng = np.random.default_rng(seed)
        self.x = np.linspace(8, 40, self.cols)
        self.y = np.linspace(0, 24, self.rows)
        xx, yy = np.meshgrid(self.x, self.y)
        k = 2*np.pi/32
        center = rng.uniform(5, 19)
        width = rng.uniform(3, 7)
        envelope = .35 + .45*np.exp(-.5*((yy-center)/width)**2)
        envelope += .1*np.cos(yy/5+rng.uniform(0, 2*np.pi))
        amplitude = rng.uniform(.65, 1.)
        self._truth = amplitude*np.sin(k*(xx-8))*envelope
        p = amplitude*k*np.cos(k*(xx-8))*envelope
        self.altitude = 11.+.2*np.sin(self.y/7)
        self.gain = 1.+.03*np.cos(self.y/5)
        clean = forward(p, self.x, self.altitude, self.gain)
        if mismatch:
            py = np.gradient(self._truth, self.y, axis=0)
            vertical = self.altitude[:, None]-self._truth
            actual = (vertical+xx*p)/(np.hypot(vertical, xx)*np.sqrt(1+p*p+py*py))
            # A deliberately unmodelled cross-track reflectivity perturbation.
            clean = actual*self.gain[:, None]*(1+.03*np.sin(xx/6))
        self._returns = clean+rng.normal(0, .0015, clean.shape)
        self._available = rng.random(clean.shape) > .01
        self.reset()

    def reset(self):
        self.selected = np.zeros(self.rows, dtype=bool)
        self.observed = np.full((self.rows, self.cols), np.nan)
        self.mask = np.zeros((self.rows, self.cols), dtype=bool)
        self.surface = np.zeros((self.rows, self.cols))
        self.last_solver = None
        return self.observation()

    def observation(self):
        return dict(intensity=self.observed.copy(), mask=self.mask.copy(),
                    selected=self.selected.copy(), remaining=self.budget-int(self.selected.sum()))

    def state(self):
        # Deliberately small policy: coverage-only, no truth or error in state.
        return sum((1 << i) for i in np.flatnonzero(self.selected))

    def score(self):
        error = self.surface-self._truth
        return dict(rmse_m=float(np.sqrt(np.mean(error**2))),
                    mae_m=float(np.mean(np.abs(error))),
                    max_abs_m=float(np.max(np.abs(error))))

    def step(self, action):
        if self.selected.sum() >= self.budget:
            raise ValueError('Episode is complete')
        if not isinstance(action, (int, np.integer)) or not 0 <= action < self.rows or self.selected[action]:
            raise ValueError('Action must be a previously unmeasured row index')
        before = self.score()['rmse_m']
        self.selected[action] = True
        self.observed[action] = self._returns[action]
        self.mask[action] = self._available[action]
        z, _, valid, report = reconstruct(self.observed, self.x, self.y,
            self.altitude, self.gain, mask=self.mask, smooth_x=.1, smooth_y=.05,
            max_slope=.35, max_iterations=1400)
        if not report['converged']:
            raise RuntimeError('Surface solver did not converge')
        self.surface, self.last_solver = z, report
        # Ground truth is allowed in simulator training reward, never in policy input.
        reward = before-self.score()['rmse_m']-.001
        done = int(self.selected.sum()) == self.budget
        return self.observation(), float(reward), done, {'solver': report}


def choose(q, env, rng, epsilon=0.):
    available = np.flatnonzero(~env.selected)
    if rng.random() < epsilon:
        return int(rng.choice(available))
    values = q[env.state(), available]
    best = available[np.isclose(values, values.max(), atol=1e-12, rtol=0)]
    return int(rng.choice(best))


def train(episodes, seed=31):
    if episodes < 1: raise ValueError('episodes must be positive')
    q = np.zeros((1 << SonarEnv.rows, SonarEnv.rows), dtype=np.float32)
    rng = np.random.default_rng(seed)
    history = []
    for episode in range(episodes):
        env = SonarEnv(seed=1000+episode)
        initial = env.score()['rmse_m']
        total_reward = 0.
        epsilon = .8-.7*episode/max(episodes-1, 1)
        for _ in range(env.budget):
            state = env.state()
            action = choose(q, env, rng, epsilon)
            _, reward, done, _ = env.step(action)
            future = 0. if done else float(q[env.state(), ~env.selected].max())
            # gamma=1 makes reward telescope to terminal RMSE reduction minus cost.
            q[state, action] += .3*(reward+future-q[state, action])
            total_reward += reward
        history.append(dict(episode=episode, initial_rmse_m=initial,
                            final_rmse_m=env.score()['rmse_m'], reward=total_reward))
    return q, history


def rollout(q, seed, strategy, mismatch=False, full=False):
    env = SonarEnv(seed, budget=12 if full else 4, mismatch=mismatch)
    rng = np.random.default_rng(seed+99999)
    uniform = np.linspace(0, env.rows-1, env.budget).round().astype(int)
    trace = [dict(step=0, action=None, **env.score())]
    for step in range(env.budget):
        if strategy == 'q_learning': action = choose(q, env, rng)
        elif strategy == 'random': action = int(rng.choice(np.flatnonzero(~env.selected)))
        else: action = int(uniform[step])
        _, reward, _, _ = env.step(action)
        trace.append(dict(step=step+1, action=action, reward=reward, **env.score()))
    return env, trace


def run(output, episodes=120, test_count=12):
    if test_count < 2: raise ValueError('test_count must be at least 2')
    start = time.perf_counter()
    q, history = train(episodes)
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(output/'policy.npz', q=q)
    metrics, traces = {}, {}
    for mismatch in (False, True):
        scenario = 'matched_model' if not mismatch else 'geometry_and_reflectivity_mismatch'
        metrics[scenario] = {}
        for strategy in ('uniform', 'random', 'q_learning', 'full_sampling'):
            scores = []
            for index in range(test_count):
                env, trace = rollout(q, 10000+index, strategy, mismatch,
                                     full=strategy == 'full_sampling')
                scores.append(env.score())
                if index == 0: traces[f'{scenario}/{strategy}'] = trace
                if index == 0 and strategy == 'q_learning' and not mismatch:
                    example, example_trace = env, trace
            metrics[scenario][strategy] = {
                key: float(np.mean([s[key] for s in scores])) for key in scores[0]}
            metrics[scenario][strategy].update(
                rmse_std_m=float(np.std([s['rmse_m'] for s in scores])),
                rmse_each_m=[s['rmse_m'] for s in scores],
                ping_budget=12 if strategy == 'full_sampling' else 4)
    report = dict(training_episodes=episodes, training_seeds=[1000, 1000+episodes-1],
        test_seeds=[10000,10000+test_count-1], test_terrains=test_count,
        policy='tabular Q-learning, 4096 coverage states x 12 actions, float32',
        reward='previous RMSE - new RMSE - 0.001 per ping; gamma=1',
        truth_access='training reward and offline evaluation only; actions use coverage mask only',
        elapsed_seconds=round(time.perf_counter()-start, 3),
        note='Simulation only. Full sampling has triple the budget; not a fair-cost competitor. '
             'Coverage-only policy learns a sampling schedule, not intensity-adaptive vessel control.',
        results=metrics)
    (output/'metrics.json').write_text(json.dumps(report,indent=2)+'\n')
    (output/'training.json').write_text(json.dumps(history,indent=2)+'\n')
    (output/'example_traces.json').write_text(json.dumps(traces,indent=2)+'\n')
    np.savez_compressed(output/'example.npz',x=example.x,y=example.y,
        truth=example._truth,reconstruction=example.surface,
        measured_intensity=example.observed,measurement_mask=example.mask,
        selected_rows=example.selected,altitude=example.altitude,gain=example.gain)
    plot(output,example,history,report)
    return report


def plot(output, env, history, report):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1,4,figsize=(16,4),constrained_layout=True)
    for ax,data,title,cmap in zip(axes,[env._truth,env.mask.astype(float),env.surface,env.surface-env._truth],
        ['Simulator truth (m)','Actually sampled cells','Q-learning reconstruction (m)','Error (m)'],
        ['terrain','gray','terrain','coolwarm']):
        limits = dict(vmin=float(env._truth.min()), vmax=float(env._truth.max())) if 'truth' in title.lower() or 'reconstruction' in title.lower() else {}
        im=ax.pcolormesh(env.x,env.y,data,shading='auto',cmap=cmap,**limits)
        fig.colorbar(im,ax=ax);ax.set(title=title,xlabel='Cross track (m)',ylabel='Along track (m)')
    fig.savefig(output/'reconstruction.png',dpi=150);plt.close(fig)
    fig,axes=plt.subplots(1,2,figsize=(12,4),constrained_layout=True)
    axes[0].plot([h['final_rmse_m'] for h in history],alpha=.5,label='Episode terminal RMSE')
    window=min(15,len(history))
    axes[0].plot(np.arange(window-1,len(history)),np.convolve([h['final_rmse_m'] for h in history],np.ones(window)/window,mode='valid'),label=f'{window}-episode mean')
    axes[0].set(xlabel='Training episode (different terrain each episode)',ylabel='RMSE (m)',title='Training: simulator reward, not test accuracy');axes[0].legend()
    names=['uniform','random','q_learning','full_sampling']
    for offset,(scenario,results) in zip([-.18,.18],report['results'].items()):
        axes[1].bar(np.arange(4)+offset,[results[n]['rmse_m'] for n in names],.36,
                    yerr=[results[n]['rmse_std_m'] for n in names],label=scenario)
    axes[1].set_xticks(np.arange(4),['Uniform (4)','Random (4)','Q-learning (4)','Full (12)'])
    axes[1].set(ylabel='Held-out RMSE mean ± std (m)',title='Independent test terrain seeds');axes[1].legend(fontsize=7)
    fig.savefig(output/'evaluation.png',dpi=150);plt.close(fig)


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path('outputs/simulation'))
    p.add_argument('--episodes',type=int,default=120)
    p.add_argument('--test-count',type=int,default=12)
    args=p.parse_args()
    report=run(args.output,args.episodes,args.test_count)
    print(json.dumps(report,indent=2))
