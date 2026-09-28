
"""IT5005: knowledge-base contribution (Q1 and Q4).

The two builders are complete. FC/BC solver stubs are deliberately reserved
for the other group member. Only the supplied logic and utility modules are
imported; neither support file nor atom() is modified.
"""

from utils import collections
from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def _validate_inputs(n, box_h, box_w, givens):
    """Reject malformed inputs and directly conflicting clues.

    This checks local consistency, not existence or uniqueness of a solution.
    The caller's dictionary is read only and is never changed.
    """
    if any(type(x) is not int or x < 1 for x in (n, box_h, box_w)):
        raise ValueError('Grid and box dimensions must be positive integers.')
    if box_h * box_w != n:
        raise ValueError('box_h * box_w must equal n.')
    if not isinstance(givens, dict):
        raise ValueError('givens must be a dictionary of (row, column): value.')
    for cell, value in givens.items():
        if (not isinstance(cell, tuple) or len(cell) != 2
                or any(type(x) is not int or not 1 <= x <= n for x in cell)
                or type(value) is not int or not 1 <= value <= n):
            raise ValueError('Clues must use integer rows, columns and values in 1..n.')
    for (r, c), value in givens.items():
        for peer in _peers(n, box_h, box_w, r, c):
            if givens.get(peer) == value:
                raise ValueError('Conflicting givens in a row, column or box.')


def _peers(n, box_h, box_w, r, c):
    """Return sorted, distinct cells sharing a row, column or box with (r,c)."""
    cells = {(r, k) for k in range(1, n + 1)}
    cells.update((k, c) for k in range(1, n + 1))
    r0 = ((r - 1) // box_h) * box_h + 1
    c0 = ((c - 1) // box_w) * box_w + 1
    cells.update((rr, cc) for rr in range(r0, r0 + box_h)
                 for cc in range(c0, c0 + box_w))
    cells.discard((r, c))
    return sorted(cells)


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    _validate_inputs(n, box_h, box_w, givens)
    kb = PropKB()
    values = range(1, n + 1)
    symbols = {(r, c, v): atom('Is', r, c, v)
               for r in values for c in values for v in values}
    for r in values:
        for c in values:
            # At least one value.
            kb.tell(associate('|', [symbols[r, c, v] for v in values]))

            for v in values:
                for w in range(v + 1, n + 1):
                    # ~symbols[r, c, v] | ~symbols[r, c, w] is false when both symbols[r, c, v] and symbols[r, c, w] are true.
                    # Adding this on every pair of distinct values restricts the cell to have at most one value.
                    kb.tell(~symbols[r, c, v] | ~symbols[r, c, w])

            # Add exclusion clauses for all peers of the current cell.
            for rr, cc in _peers(n, box_h, box_w, r, c):
                if (r, c) < (rr, cc): # prevent duplication of exclusion clauses
                    for v in values:
                        # ~symbols[r, c, v] | ~symbols[rr, cc, v] is false when both symbols[r, c, v] and symbols[rr, cc, v] are true.
                        # This clause ensures that no two peers can have the same value.
                        kb.tell(~symbols[r, c, v] | ~symbols[rr, cc, v])

    for (r, c), v in sorted(givens.items()):
        kb.tell(symbols[r, c, v])
    return kb


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    _validate_inputs(n, box_h, box_w, givens)
    kb = PropDefiniteKB()
    values = range(1, n + 1)
    is_value = {(r, c, v): atom('Is', r, c, v)
                for r in values for c in values for v in values}
    not_value = {(r, c, v): atom('Not', r, c, v)
                 for r in values for c in values for v in values}
    # Encode the given cells as definite facts in the knowledge base.
    for (r, c), v in sorted(givens.items()):
        kb.tell(is_value[r, c, v])

    for r in values:
        for c in values:
            peers = _peers(n, box_h, box_w, r, c)
            for v in values:
                # Not... is a positive atom representing an established
                for w in values:
                    if w != v:
                        # Eliminate w as a possible value for this cell if v is known.
                        kb.tell(Expr('==>', is_value[r, c, v], not_value[r, c, w]))
                for rr, cc in peers:
                    # Eliminate v as a possible value for each peer if v is known for this cell.
                    kb.tell(Expr('==>', is_value[r, c, v], not_value[rr, cc, v]))
                eliminated = [not_value[r, c, w] for w in values if w != v]
                if eliminated:
                    # If all other values have been eliminated, then v must be the value for this cell.
                    kb.tell(Expr('==>', associate('&', eliminated), is_value[r, c, v]))
                else:
                    # The 1x1 case has only one possible value, unconditionally.
                    if is_value[r, c, v] not in kb.clauses:
                        kb.tell(is_value[r, c, v])
    return kb


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solution = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            matches = [
                v for v in range(1, n + 1)
                if pl_fc_entails(kb, atom('Is', r, c, v))
            ]

            if len(matches) != 1:
                raise ValueError(
                    f'Could not derive exactly one value for cell {(r, c)}.'
                )

            solution[(r, c)] = matches[0]

    return solution


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """

    from collections import defaultdict
    clauses = tuple(kb.clauses)
    # create a cache that can be shared across multiple calls
    cache = getattr(kb, '_bc_cache', None)
    if cache is None or cache[0] != clauses:
        rules = defaultdict(list)
        proven = set() # cache of goals already shown true (memoization)
        for clause in clauses:
            premises, conclusion = parse_definite_clause(clause)
            rules[conclusion].append(premises)
            if not premises:
                proven.add(conclusion)
        cache = (clauses, rules, proven)
        kb._bc_cache = cache
    _, rules, proven = cache

    def prove(goal, path):
        if goal in proven: # early exit if already proven
            return True
        if goal in path: # cycle
            return False

        path.add(goal)
        try:
            for premises in rules.get(goal, ()):
                # Since all([]) returns True, facts with no premises are automatically proven
                if all(prove(p, path) for p in premises):
                    proven.add(goal)
                    return True
            return False
        finally:
            path.remove(goal) # backtrack

    return prove(query, set())


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solution = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            matches = [
                v for v in range(1, n + 1)
                if pl_bc_entails(kb, atom('Is', r, c, v))
            ]

            if len(matches) != 1:
                raise ValueError(
                    f'Could not derive exactly one value for cell {(r, c)}.'
                )

            solution[(r, c)] = matches[0]

    return solution
