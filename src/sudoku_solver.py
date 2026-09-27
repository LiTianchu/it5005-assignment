
"""IT5005: knowledge-base contribution (Q1 and Q4).

The two builders are complete. FC/BC solver stubs are deliberately reserved
for the other group member. Only the supplied logic and utility modules are
imported; neither support file nor atom() is modified.
"""

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
            # At least one value, then at most one value per cell.
            kb.tell(associate('|', [symbols[r, c, v] for v in values]))
            for v in values:
                for w in range(v + 1, n + 1):
                    kb.tell(~symbols[r, c, v] | ~symbols[r, c, w])
            # Peer pairs are unordered: emit each exclusion only once,
            # even if the cells share both a row/column and a box.
            for rr, cc in _peers(n, box_h, box_w, r, c):
                if (r, c) < (rr, cc):
                    for v in values:
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
    for (r, c), v in sorted(givens.items()):
        kb.tell(is_value[r, c, v])
    for r in values:
        for c in values:
            peers = _peers(n, box_h, box_w, r, c)
            for v in values:
                # Not... is a positive atom representing an established
                # elimination, not Python 'not' or a negated Is literal.
                for w in values:
                    if w != v:
                        kb.tell(Expr('==>', is_value[r, c, v], not_value[r, c, w]))
                for rr, cc in peers:
                    kb.tell(Expr('==>', is_value[r, c, v], not_value[rr, cc, v]))
                eliminated = [not_value[r, c, w] for w in values if w != v]
                if eliminated:
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
    raise NotImplementedError(
        'solve_full_grid_fc: solve every cell with forward chaining'
    )


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
    raise NotImplementedError(
        'pl_bc_entails: implement backward chaining, soundly'
    )


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    raise NotImplementedError(
        'solve_full_grid_bc: solve every cell with backward chaining'
    )
