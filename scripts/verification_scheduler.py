"""Dependency-aware bounded scheduling for independent Lean -j1 processes.
Results are returned in inventory order regardless of completion order.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait


def run_dag(order, dependencies, action, jobs=1, notify=None):
    if jobs not in (1, 2):
        raise ValueError('jobs must be 1 or 2')
    if len(set(order)) != len(order):
        raise ValueError('duplicate module in inventory')
    inventory = set(order)
    if set(dependencies) != inventory or any(d not in inventory for ds in dependencies.values() for d in ds):
        raise ValueError('dependency inventory mismatch')
    pending = list(order)
    running = {}
    finished = {}
    ranks = {name: i for i, name in enumerate(order)}

    def record(name, result):
        finished[name] = result
        if notify is not None:
            notify(name, result)

    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            progressed = True
            while progressed:
                progressed = False
                for name in list(pending):
                    if not all(d in finished for d in dependencies[name]):
                        continue
                    if any(finished[d]['status'] != 'PASS' for d in dependencies[name]):
                        pending.remove(name)
                        record(name, {'status': 'SKIP_FAILED_DEPENDENCY'})
                        progressed = True
                    elif len(running) < jobs:
                        pending.remove(name)
                        running[executor.submit(action, name)] = name
                        progressed = True
            if running:
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in sorted(completed, key=lambda f: ranks[running[f]]):
                    name = running.pop(future)
                    try:
                        result = future.result()
                    except Exception as exc:
                        result = {'status': 'FAIL', 'error': str(exc)}
                    record(name, result)
            elif pending:
                raise ValueError('cyclic or unresolved dependencies: '+repr(pending))
    return {name: finished[name] for name in order}
