#!/usr/bin/env python3
"""Compile, audit and replay the published Theorem 13 pilot; fail closed."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', required=True, type=Path)
    parser.add_argument('--checker', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--compat-library', type=Path,
                        help='Optional disclosed local process-path workaround; forbidden in CI.')
    parser.add_argument('--require-standard-runtime', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    toolchain = args.toolchain.resolve()
    checker = args.checker.resolve()
    out = (args.output or root / 'verification/run').resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['PATH'] = str(toolchain / 'bin') + os.pathsep + env.get('PATH', '')
    env.pop('LEAN_PATH', None)
    env.pop('LD_PRELOAD', None)
    env.pop('LD_LIBRARY_PATH', None)
    env.pop('LEAN_SYSROOT', None)
    if args.compat_library:
        env['LD_PRELOAD'] = str(args.compat_library.resolve())
    records = []
    result = {
        'schema': 'causal-foundations-lean-verification-v2',
        'status': 'RUNNING',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'published_numbered_endpoints_completed': ['Theorem 13'],
        'whole_paper_formalized': False,
        'runtime_compatibility': {'used': bool(args.compat_library)},
        'external_peer_review': False,
        'independent_kernel_verification': False,
        'semantic_alignment': 'ASSISTANT_REVIEW_NOT_MECHANICALLY_CERTIFIED',
        'commands': records,
    }

    def save():
        (out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')

    def run(label, command, cwd=root, extra=None, expect_failure=False):
        command = [str(x) for x in command]
        local_env = dict(env)
        local_env.update(extra or {})
        proc = subprocess.run(command, cwd=cwd, env=local_env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=300)
        log = out / (label + '.log')
        log.write_text(proc.stdout)
        passed = proc.returncode == 0
        if expect_failure:
            passed = (proc.returncode != 0 and 'error:' in proc.stdout
                      and 'rfl' in proc.stdout and '2 = 3' in proc.stdout)
        records.append({'label': label, 'argv': command, 'returncode': proc.returncode,
                        'expected_rejection': expect_failure, 'passed': passed,
                        'log': log.name, 'log_sha256': digest(log)})
        save()
        print(label + ': ' + ('PASS' if passed else 'FAIL'), flush=True)
        require(passed, proc.stdout or 'Command failed: ' + label)
        return proc.stdout

    def audit(text, expected):
        found = {}
        for line in text.splitlines():
            match = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
            if match:
                found[match[1]] = []
                continue
            match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
            if match:
                found[match[1]] = [x.strip() for x in match[2].split(',') if x.strip()]
        require(set(found) == set(expected), 'Audited declaration set differs from expectation.')
        for name, axioms in found.items():
            require(set(axioms) == set(expected[name]), 'Unexpected axiom dependency: ' + name)
            require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'},
                    'Nonstandard axiom: ' + name)
        return found

    save()
    try:
        require(not (args.compat_library and (args.require_standard_runtime
                    or os.environ.get('GITHUB_ACTIONS') == 'true')),
                'The standard environment check forbids a compatibility library.')
        pins = json.loads((root / 'verification/TOOLCHAIN_LOCK.json').read_text())
        expected = json.loads((root / 'verification/EXPECTED_AXIOMS.json').read_text())
        expected_main = {k: v for k, v in expected.items() if '.Tests.' not in k}
        expected_boundary = {k: v for k, v in expected.items() if '.Tests.' in k}
        proof_files = ['CausalFoundations.lean', 'CausalFoundations/ResourcePrefix.lean',
                       'AxiomAudit.lean', 'BoundaryTests.lean']
        for file in proof_files:
            require(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|skipKernelTC',
                                  (root / file).read_text()), 'Forbidden proof token: ' + file)
        for filename, prefix, wanted in [
            ('CausalFoundations/ResourcePrefix.lean', 'CausalFoundations.', expected_main),
            ('BoundaryTests.lean', 'CausalFoundations.Tests.', expected_boundary),
        ]:
            names = re.findall(r'^theorem\s+([A-Za-z0-9_]+)', (root / filename).read_text(), re.M)
            require({prefix + name for name in names} == set(wanted),
                    'A declared theorem is missing from the axiom audit: ' + filename)
        lock = json.loads((root / 'SOURCE_LOCK.json').read_text())
        for volume in lock['volumes']:
            path = root.parent / volume['path']
            require(path.stat().st_size == volume['bytes'] and digest(path) == volume['sha256'],
                    'Published PDF differs from the locked source: ' + volume['path'])
        result['source_binding'] = {'status': 'PASS', 'lock_sha256': digest(root / 'SOURCE_LOCK.json')}
        require((root / 'lean-toolchain').read_text().strip() == pins['lean_toolchain'],
                'Toolchain version is not pinned correctly.')
        require(digest(toolchain / 'bin/lean') == pins['lean_executable_sha256'],
                'Lean executable does not match the official pinned toolchain.')
        require(digest(toolchain / 'lib/lean/libleanshared.so') == pins['lean_shared_runtime_sha256'],
                'Lean shared runtime does not match the official pinned toolchain.')
        result['source_sha256'] = {x: digest(root / x) for x in proof_files}
        result['checked_commit'] = subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        result['github_run_url'] = (os.environ.get('GITHUB_SERVER_URL', '') + '/'
            + os.environ.get('GITHUB_REPOSITORY', '') + '/actions/runs/'
            + os.environ['GITHUB_RUN_ID']) if os.environ.get('GITHUB_RUN_ID') else None
        version = run('01_version', ['lean', '--version'])
        require('version 4.24.0' in version and pins['lean_commit'] in version,
                'Unexpected Lean version or commit.')
        run('02_build', ['lake', 'build', 'CausalFoundations'])
        ax = audit(run('03_axioms', ['lake', 'env', 'lean', 'AxiomAudit.lean']), expected_main)
        bx = audit(run('04_boundary_tests', ['lake', 'env', 'lean', 'BoundaryTests.lean',
                   '-o', '.lake/build/lib/lean/BoundaryTests.olean']), expected_boundary)
        run('05_rejected_false_statement', ['lake', 'env', 'lean', 'NegativeControl.lean'],
            expect_failure=True)
        checker_commit = run('06_checker_identity', ['git', '-C', checker, 'rev-parse', 'HEAD']).strip()
        require(checker_commit == pins['checker_commit'], 'Unexpected lean4checker commit.')
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                    cwd=checker, text=True).strip(), 'The checker has modified tracked sources.')
        run('07_checker_build', ['lake', 'build', 'Lean4Checker'], cwd=checker)

        def replay(label, project, module):
            paths = os.pathsep.join([str(project / '.lake/build/lib/lean'),
                                    str(checker / '.lake/build/lib/lean')])
            return run(label, ['lean', '--run', checker / 'Main.lean', '--fresh', '-v', module],
                       cwd=project, extra={'LEAN_PATH': paths})

        replay('08_fresh_kernel_replay', root, 'CausalFoundations.ResourcePrefix')
        replay('09_boundary_kernel_replay', root, 'BoundaryTests')
        with tempfile.TemporaryDirectory(prefix='cf-lean-cold-') as temp:
            cold = Path(temp)
            for name in proof_files + ['NegativeControl.lean', 'lean-toolchain', 'lakefile.toml']:
                target = cold / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(root / name, target)
            run('10_cold_build', ['lake', 'build', 'CausalFoundations'], cwd=cold)
            cold_ax = audit(run('11_cold_axioms', ['lake', 'env', 'lean', 'AxiomAudit.lean'],
                                cwd=cold), expected_main)
            require(ax == cold_ax, 'Cold rebuild changed the axiom audit.')
            replay('12_cold_fresh_kernel_replay', cold, 'CausalFoundations.ResourcePrefix')
        result.update({
            'status': 'PASS_LOCAL_WITH_DISCLOSED_COMPATIBILITY' if args.compat_library
                      else 'PASS_STANDARD_RUNTIME',
            'main_proof_declarations_audited': len(ax),
            'boundary_test_theorems_audited': len(bx),
            'axioms': {**ax, **bx}, 'custom_axioms': [], 'omitted_proofs': [],
            'native_evaluation_axioms': [], 'theorem13_axioms': ax['CausalFoundations.theorem13'],
            'toolchain': {'version': version.strip(), 'lock_sha256': digest(root / 'verification/TOOLCHAIN_LOCK.json')},
            'checker': {'commit': checker_commit, 'mode': '--fresh; same Lean kernel'},
            'cold_rebuild': {'source_copy_only': True, 'axiom_outputs_equal': True,
                             'fresh_kernel_replay_passed': True},
        })
    except Exception as error:
        result['status'] = 'FAIL'
        result['error'] = str(error)
        raise
    finally:
        result['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(json.dumps({'status': result['status'], 'steps': len(records),
                      'theorem13_axioms': result['theorem13_axioms']}), flush=True)


if __name__ == '__main__':
    main()
