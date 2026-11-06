import sys
import unittest
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'simulation'))
from experiment import SonarEnv, choose


class SimulationTests(unittest.TestCase):
    def test_no_truth_in_observation_and_only_selected_row_is_returned(self):
        env=SonarEnv(123)
        observation=env.observation()
        self.assertEqual(set(observation),{'intensity','mask','selected','remaining'})
        self.assertTrue(np.isnan(observation['intensity']).all())
        self.assertFalse(observation['mask'].any())
        before=env.score()['rmse_m']
        observation,reward,done,info=env.step(5)
        self.assertFalse(done)
        self.assertEqual(env.state(),1<<5)
        self.assertEqual(observation['remaining'],3)
        self.assertTrue(np.isnan(observation['intensity'][np.arange(12)!=5]).all())
        self.assertAlmostEqual(reward,before-env.score()['rmse_m']-.001)
        self.assertTrue(info['solver']['converged'])
        observation['selected'][:]=False
        self.assertTrue(env.selected[5])

    def test_reward_telescopes_and_finished_episode_rejects_actions(self):
        env=SonarEnv(123)
        initial=env.score()['rmse_m'];total=0.
        for action in [0,4,8,11]:
            _,reward,done,_=env.step(action);total+=reward
        self.assertTrue(done)
        self.assertAlmostEqual(total,initial-env.score()['rmse_m']-.004)
        with self.assertRaises(ValueError):env.step(2)

    def test_seed_reproducibility_and_no_repeated_action(self):
        a,b=SonarEnv(555),SonarEnv(555)
        a.step(2);b.step(2)
        np.testing.assert_array_equal(a.surface,b.surface)
        with self.assertRaises(ValueError):a.step(2)
        with self.assertRaises(ValueError):a.step(-1)
        q=np.zeros((4096,12));q[a.state(),2]=100
        self.assertNotEqual(choose(q,a,np.random.default_rng(1)),2)
        np.testing.assert_array_equal(a._truth[:,0],np.zeros(12))


if __name__=='__main__':unittest.main()
