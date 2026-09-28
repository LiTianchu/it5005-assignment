"""Regression tests for recursive backward chaining and its answer cache."""

import json
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))

from logic_ import PropDefiniteKB, expr, pl_fc_entails
from sudoku_solver import atom, build_definite_kb, pl_bc_entails, solve_full_grid_bc


def make_kb(*clauses):
    kb = PropDefiniteKB()
    for clause in clauses:
        kb.tell(expr(clause))
    return kb


class RecursiveBackwardChainingTests(unittest.TestCase):
    def test_unsupported_cycles_and_missing_facts(self):
        kb = make_kb('B ==> A', 'A ==> B')
        for name in ('A', 'B', 'Missing'):
            self.assertFalse(pl_bc_entails(kb, expr(name)))

    def test_retry_failure_after_alternative_proof_breaks_cycle(self):
        kb = make_kb('B ==> A', 'Seed ==> A', 'A ==> B',
                     '(A & B) ==> Result', 'Seed')
        # Proving A first visits B through a cycle; Seed then proves A.
        # B must be reconsidered before Result can be established.
        self.assertTrue(pl_bc_entails(kb, expr('Result')))
        self.assertTrue(pl_bc_entails(kb, expr('B')))

    def test_failed_query_does_not_cache_provable_subgoal_as_false(self):
        kb = make_kb('B ==> A', 'Seed ==> A', 'A ==> B',
                     '(A & Missing) ==> Result', 'Seed')
        self.assertFalse(pl_bc_entails(kb, expr('Result')))
        self.assertTrue(pl_bc_entails(kb, expr('B')))

    def test_conjunction_alternatives_and_repeated_premises(self):
        kb = make_kb('A', '(A & Missing) ==> B', 'A ==> B',
                     '(A & Missing) ==> C', '(A & A) ==> D')
        for name, expected in [('B', True), ('C', False), ('D', True)]:
            self.assertEqual(pl_bc_entails(kb, expr(name)), expected)

    def test_stops_after_success_without_exploring_unrelated_rules(self):
        kb = make_kb('Seed', 'Seed ==> A', 'X ==> A', 'Y ==> X', 'X ==> Y')
        self.assertTrue(pl_bc_entails(kb, expr('A')))
        self.assertNotIn(expr('X'), kb._bc_table[2])
        self.assertNotIn(expr('Y'), kb._bc_table[2])

    def test_cache_invalidates_after_tell_and_retract(self):
        kb = make_kb('A ==> B', 'B ==> A')
        self.assertFalse(pl_bc_entails(kb, expr('B')))
        kb.tell(expr('A'))
        self.assertTrue(pl_bc_entails(kb, expr('B')))
        kb.retract(expr('A'))
        self.assertFalse(pl_bc_entails(kb, expr('B')))

    def test_chain_and_cycle_within_python_recursion_limit(self):
        kb = make_kb('P0')
        for i in range(300):
            kb.tell(expr(f'P{i} ==> P{i + 1}'))
        self.assertTrue(pl_bc_entails(kb, expr('P300')))
        kb.retract(expr('P0'))
        kb.tell(expr('P300 ==> P0'))
        self.assertFalse(pl_bc_entails(kb, expr('P300')))
        kb.tell(expr('Seed ==> P150'))
        kb.tell(expr('Seed'))
        self.assertTrue(pl_bc_entails(kb, expr('P300')))

    def test_generated_kbs_agree_with_library_forward_chaining(self):
        rng = random.Random(42)
        names = list('ABCDEFGH')
        for case in range(300):
            kb = PropDefiniteKB()
            for name in names:
                if rng.random() < 0.25:
                    kb.tell(expr(name))
            for _ in range(24):
                premises = rng.sample(names, rng.randint(1, 3))
                clause = expr(f'({" & ".join(premises)}) ==> {rng.choice(names)}')
                if clause not in kb.clauses:
                    kb.tell(clause)
            rng.shuffle(names)
            for name in names:
                with self.subTest(case=case, query=name):
                    self.assertEqual(pl_bc_entails(kb, expr(name)),
                                     pl_fc_entails(kb, expr(name)))

    def test_all_puzzles_all_candidates_and_full_grid_solver(self):
        pool = json.loads((Path(__file__).resolve().parents[1]
                           / 'src' / 'puzzles.json').read_text())
        n, box_h, box_w = pool['n'], pool['box_h'], pool['box_w']
        for puzzle in pool['puzzles']:
            givens = {tuple(map(int, k.split('_'))): v
                      for k, v in puzzle['givens'].items()}
            solution = {tuple(map(int, k.split('_'))): v
                        for k, v in puzzle['solution'].items()}
            kb = build_definite_kb(n, box_h, box_w, givens)
            for (r, c), expected in solution.items():
                for v in range(1, n + 1):
                    self.assertEqual(pl_bc_entails(kb, atom('Is', r, c, v)),
                                     v == expected)
            self.assertEqual(solve_full_grid_bc(n, box_h, box_w, givens), solution)


if __name__ == '__main__':
    unittest.main()
