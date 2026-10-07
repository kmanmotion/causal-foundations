#!/usr/bin/env python3
"""Verify published Theorem 3 with pinned actual probability dependencies."""
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
import time


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
    parser.add_argument('--compat-library', type=Path)
    parser.add_argument('--require-standard-runtime', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    core = root.parent
    toolchain, checker = args.toolchain.resolve(), args.checker.resolve()
    out = (args.output or root / 'verification/run').resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['PATH'] = str(toolchain / 'bin') + os.pathsep + env.get('PATH', '')
    for key in ['LEAN_PATH', 'LD_PRELOAD', 'LD_LIBRARY_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    if args.compat_library:
        env['LD_PRELOAD'] = str(args.compat_library.resolve())
    records = []
    result = {
        'schema': 'causal-foundations-probability-verification-v1',
        'status': 'RUNNING', 'started_utc': datetime.now(timezone.utc).isoformat(),
        'published_numbered_endpoints_targeted': ['Theorem 3'],
        'whole_paper_formalized': False,
        'runtime_compatibility': {'used': bool(args.compat_library)},
        'external_peer_review': False, 'independent_kernel_verification': False,
        'semantic_alignment': 'ASSISTANT_REVIEW_NOT_MECHANICALLY_CERTIFIED',
        'commands': records,
    }

    def save():
        (out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')

    def run(label, command, cwd=root, extra=None, expect_failure=False, timeout=600):
        command = [str(x) for x in command]
        local_env = dict(env)
        local_env.update(extra or {})
        started = time.monotonic()
        proc = subprocess.run(command, cwd=cwd, env=local_env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
        log = out / (label + '.log')
        log.write_text(proc.stdout)
        passed = proc.returncode == 0
        if expect_failure:
            passed = (proc.returncode != 0 and 'error:' in proc.stdout
                      and 'rfl' in proc.stdout and '2 = 3' in proc.stdout)
        records.append({'label': label, 'argv': command, 'returncode': proc.returncode,
                        'expected_rejection': expect_failure, 'passed': passed,
                        'elapsed_seconds': round(time.monotonic() - started, 3),
                        'log': log.name, 'log_sha256': digest(log)})
        save()
        print(label + ': ' + ('PASS' if passed else 'FAIL'), flush=True)
        require(passed, proc.stdout or 'Command failed: ' + label)
        return proc.stdout

    def declarations(filename):
        namespaces, names = [], []
        for line in (root / filename).read_text().splitlines():
            match = re.match(r'^namespace\s+([A-Za-z0-9_.]+)', line)
            if match:
                namespaces.append(match[1])
            match = re.match(r'^theorem\s+([A-Za-z0-9_]+)', line)
            if match:
                names.append('.'.join(namespaces + [match[1]]))
            if re.fullmatch(r'end(?:\s+[A-Za-z0-9_.]+)?\s*', line):
                namespaces.pop()
        return names

    def audit(text, expected):
        found = {}
        pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])"
        for match in re.finditer(pattern, text):
            name, dependencies = match.groups()
            require(name not in found, 'Duplicate audit output: ' + name)
            found[name] = [x.strip() for x in (dependencies or '').split(',') if x.strip()]
        require(set(found) == set(expected), 'Audited declaration set differs from expectation.')
        for name, axioms in found.items():
            require(set(axioms) == set(expected[name]), 'Unexpected dependency: ' + name)
            require(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'},
                    'Nonstandard dependency: ' + name)
        return found

    save()
    try:
        require(not (args.compat_library and (args.require_standard_runtime
                    or os.environ.get('GITHUB_ACTIONS') == 'true')),
                'Standard runtime verification forbids a compatibility library.')
        pins = json.loads((core / 'verification/TOOLCHAIN_LOCK.json').read_text())
        lock = json.loads((root / 'verification/DEPENDENCY_LOCK.json').read_text())
        expected = json.loads((root / 'verification/EXPECTED_AXIOMS.json').read_text())
        modules = {'CausalFoundationsProbability.FirstHitting':
                   'CausalFoundationsProbability/FirstHitting.lean',
                   'FirstHittingTests': 'FirstHittingTests.lean'}
        proof_files = ['CausalFoundationsProbability.lean', 'AxiomAudit.lean', 'ProbabilityReplayAll.lean',
                       *modules.values()]
        names = {module: declarations(file) for module, file in modules.items()}
        all_names = [name for ns in names.values() for name in ns]
        require(len(all_names) == len(set(all_names)), 'Duplicate theorem names.')
        require(set(all_names) == set(expected), 'Declared theorem missing from the registry.')
        for file in proof_files:
            require(not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|skipKernelTC',
                                  (root / file).read_text()), 'Forbidden proof token: ' + file)
        require(digest(root / 'lake-manifest.json') == lock['manifest_sha256'],
                'Dependency manifest differs from the lock.')
        require((root / 'lean-toolchain').read_text().strip() == pins['lean_toolchain'],
                'Probability project toolchain is not pinned correctly.')
        for binary, key in [('bin/lean', 'lean_executable_sha256'),
                            ('lib/lean/libleanshared.so', 'lean_shared_runtime_sha256')]:
            require(digest(toolchain / binary) == pins[key], 'Official runtime differs: ' + binary)
        public_lock = json.loads((core / 'SOURCE_LOCK.json').read_text())
        for volume in public_lock['volumes']:
            p = core.parent / volume['path']
            require(p.stat().st_size == volume['bytes'] and digest(p) == volume['sha256'],
                    'Published PDF differs: ' + volume['path'])
        result['source_binding'] = {'status': 'PASS', 'lock_sha256': digest(core / 'SOURCE_LOCK.json')}
        result['source_sha256'] = {file: digest(root / file) for file in proof_files}
        core_expected = json.loads((core / 'verification/EXPECTED_AXIOMS.json').read_text())
        core_sources = ['CausalFoundations.lean', 'AxiomAudit.lean', 'ReplayAll.lean',
            'CausalFoundations/ResourcePrefix.lean', 'CausalFoundations/ResidualGame.lean',
            'CausalFoundations/SemanticBasis.lean', 'CausalFoundations/Representation.lean',
            'CausalFoundations/FixedSet.lean', 'CausalFoundations/OrbitErasure.lean',
            'BoundaryTests.lean', 'ResidualGameTests.lean', 'SemanticBasisTests.lean',
            'RepresentationTests.lean', 'FixedSetTests.lean', 'OrbitErasureTests.lean']
        result['core_source_sha256'] = {file: digest(core / file) for file in core_sources}
        result['core_registry_sha256'] = digest(core / 'verification/EXPECTED_AXIOMS.json')
        result['core_audited_declaration_count'] = len(core_expected)
        result['checked_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root,
                                                          text=True).strip()
        result['working_tree_dirty'] = bool(subprocess.check_output(['git', 'status', '--porcelain'],
                                                                   cwd=root, text=True).strip())
        require(os.environ.get('GITHUB_ACTIONS') != 'true' or not result['working_tree_dirty'],
                'CI must check an unchanged source checkout.')
        result['github_run_url'] = (os.environ.get('GITHUB_SERVER_URL', '') + '/'
            + os.environ.get('GITHUB_REPOSITORY', '') + '/actions/runs/'
            + os.environ['GITHUB_RUN_ID']) if os.environ.get('GITHUB_RUN_ID') else None
        version = run('01_version', ['lean', '--version'])
        require('version 4.24.0' in version and pins['lean_commit'] in version,
                'Unexpected Lean version or commit.')
        run('02_dependency_materialization', ['lake', 'resolve-deps'], timeout=900)
        repositories = []
        for dep in lock['repositories']:
            path = root / '.lake/packages' / dep['name']
            actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path, text=True).strip()
            require(actual == dep['commit'], 'Dependency commit differs: ' + dep['name'])
            require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                        cwd=path, text=True).strip(), 'Modified dependency sources: ' + dep['name'])
            repositories.append({**dep, 'tracked_sources_clean': True})
        result['dependencies'] = {'lock_sha256': digest(root / 'verification/DEPENDENCY_LOCK.json'),
                                  'manifest_sha256': lock['manifest_sha256'],
                                  'repositories': repositories}
        run('03_dependency_cache', ['lake', 'exe', 'cache', 'get', *lock['cache_roots']], timeout=1800)
        run('04_build', ['lake', 'build', 'CausalFoundationsProbability'])
        expected_main = {name: expected[name] for name in names['CausalFoundationsProbability.FirstHitting']}
        ax = audit(run('05_axioms', ['lake', 'env', 'lean', 'AxiomAudit.lean']), expected_main)
        expected_tests = {name: expected[name] for name in names['FirstHittingTests']}
        bx = audit(run('06_FirstHittingTests', ['lake', 'env', 'lean', 'FirstHittingTests.lean',
            '-o', '.lake/build/lib/lean/FirstHittingTests.olean']), expected_tests)
        run('07_rejected_false_statement', ['lake', 'env', 'lean', 'NegativeControl.lean'], expect_failure=True)
        checker_commit = run('08_checker_identity', ['git', '-C', checker, 'rev-parse', 'HEAD']).strip()
        require(checker_commit == pins['checker_commit'], 'Unexpected checker commit.')
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                    cwd=checker, text=True).strip(), 'Modified checker sources.')
        run('09_checker_build', ['lake', 'build', 'Lean4Checker'], cwd=checker)

        def replay(label, project):
            return run(label, ['lake', 'env', 'lean', '--run', checker / 'Main.lean',
                              '--fresh', '-v', 'ProbabilityReplayAll'], cwd=project,
                       extra={'LEAN_PATH': str(checker / '.lake/build/lib/lean')}, timeout=5400)

        run('10_replay_target_build', ['lake', 'env', 'lean', 'ProbabilityReplayAll.lean',
                                     '-o', '.lake/build/lib/lean/ProbabilityReplayAll.olean'])
        replay('11_fresh_all_declarations', root)
        with tempfile.TemporaryDirectory(prefix='cf-probability-cold-') as temp:
            cold_core = Path(temp) / 'lean'
            cold = cold_core / 'probability'
            for file in core_sources + ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
                target = cold_core / file
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(core / file, target)
            for file in proof_files + ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
                target = cold / file
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(root / file, target)
            packages = cold / '.lake/packages'
            packages.mkdir(parents=True)
            for dep in lock['repositories']:
                (packages / dep['name']).symlink_to(root / '.lake/packages' / dep['name'],
                                                   target_is_directory=True)
            run('12_cold_build', ['lake', 'build', 'CausalFoundationsProbability'], cwd=cold)
            cold_ax = audit(run('13_cold_axioms', ['lake', 'env', 'lean', 'AxiomAudit.lean'], cwd=cold), expected_main)
            cold_bx = audit(run('14_cold_FirstHittingTests', ['lake', 'env', 'lean', 'FirstHittingTests.lean',
                '-o', '.lake/build/lib/lean/FirstHittingTests.olean'], cwd=cold), expected_tests)
            require(ax == cold_ax and bx == cold_bx, 'Cold rebuild changed theorem dependencies.')
            run('15_cold_replay_target_build', ['lake', 'env', 'lean', 'ProbabilityReplayAll.lean',
                '-o', '.lake/build/lib/lean/ProbabilityReplayAll.olean'], cwd=cold)
            replay('16_cold_fresh_all_declarations', cold)
        result.update({
            'status': 'PASS_LOCAL_WITH_DISCLOSED_COMPATIBILITY' if args.compat_library else 'PASS_STANDARD_RUNTIME',
            'published_numbered_endpoints_completed': ['Theorem 3'],
            'main_proof_declarations_audited': len(ax), 'boundary_test_theorems_audited': len(bx),
            'axioms': {**ax, **bx}, 'custom_axioms': [], 'omitted_proofs': [],
            'native_evaluation_axioms': [], 'theorem3_axioms': ax['CausalFoundations.theorem3'],
            'toolchain': {'version': version.strip(), 'lock_sha256': digest(core / 'verification/TOOLCHAIN_LOCK.json')},
            'checker': {'commit': checker_commit, 'mode': '--fresh; same Lean kernel', 'target': 'ProbabilityReplayAll',
                        'scope': 'All constants, including transitive pinned Mathlib and core imports'},
            'cold_rebuild': {'project_source_copy_only': True, 'project_compiled_cache_copied': False,
                             'external_pinned_dependency_cache_reused': True,
                             'axiom_outputs_equal': True, 'fresh_kernel_replay_passed': True},
        })
    except Exception as error:
        result['status'], result['error'] = 'FAIL', str(error)
        raise
    finally:
        result['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(json.dumps({'status': result['status'], 'steps': len(records),
                      'theorem3_axioms': result['theorem3_axioms']}), flush=True)


if __name__ == '__main__':
    main()
