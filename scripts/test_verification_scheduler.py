#!/usr/bin/env python3
"""Small synthetic DAG tests; no project source or compiler is required."""
import threading
import time
import unittest
from verification_scheduler import run_dag

class SchedulerTests(unittest.TestCase):
    def test_success_and_failure(self):
        order=['a','b','c','d','e','f']
        deps={'a':[], 'b':[], 'c':['a'], 'd':['c'], 'e':['b'], 'f':['e','d']}
        for jobs in (1,2):
            active=0; peak=0; calls=[]; completed=set();lock=threading.Lock()
            def action(name):
                nonlocal active,peak
                with lock:
                    self.assertTrue(all(d in completed for d in deps[name]))
                    active+=1;peak=max(peak,active);calls.append(name)
                time.sleep(.01)
                with lock:
                    active-=1;completed.add(name)
                return {'status':'FAIL' if name=='b' else 'PASS','exit_code':1 if name=='b' else 0}
            result=run_dag(order,deps,action,jobs)
            self.assertEqual(list(result),order)
            self.assertEqual(set(calls),{'a','b','c','d'})
            self.assertEqual(result['d']['status'],'PASS')
            self.assertEqual(result['e']['status'],'SKIP_FAILED_DEPENDENCY')
            self.assertEqual(result['f']['status'],'SKIP_FAILED_DEPENDENCY')
            self.assertEqual(peak,jobs)
            self.assertEqual(active,0)
    def test_all_success(self):
        order=['a','b','c'];deps={'a':[],'b':[],'c':['a','b']}
        self.assertTrue(all(r['status']=='PASS' for r in run_dag(order,deps,lambda _: {'status':'PASS'},2).values()))
    def test_exception_skips_dependents(self):
        def action(_):raise RuntimeError('synthetic compiler failure')
        result=run_dag(['a','b'],{'a':[],'b':['a']},action,2)
        self.assertEqual(result['a']['status'],'FAIL')
        self.assertEqual(result['b']['status'],'SKIP_FAILED_DEPENDENCY')
    def test_cycle_and_invalid_jobs(self):
        with self.assertRaises(ValueError):run_dag(['a','b'],{'a':['b'],'b':['a']},lambda _: {},2)
        with self.assertRaises(ValueError):run_dag([],{},lambda _: {},3)

if __name__=='__main__':unittest.main()
