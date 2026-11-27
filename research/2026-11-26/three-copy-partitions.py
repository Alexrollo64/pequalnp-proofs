"""Check the necessary conditions for two restrictions of a shared-bit tree."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import re

GRAPH = 31917056
ROWS = [0, 2, 3, 4]
COLUMNS = [0, 1, 4]
SAMPLES = [(2, 0), (2, 1), (3, 1), (3, 4), (4, 0), (4, 1), (4, 4)]
source = Path(__file__).with_name("Mask31917056Lower.lean").read_text()
packed_prices = int(re.search(r"\((\d+) >>>", source).group(1))


def price(signature):
    return (packed_prices >> (3 * signature)) & 7


def observation(row, column):
    row_block, local_row = divmod(row, 5)
    column_block, local_column = divmod(column, 5)
    row_bit = 0 if local_row == 0 else 1 << (6 * row_block + local_row - 2)
    column_bit = 1 << (6 * column_block + 3 + COLUMNS.index(local_column))
    return row_bit | column_bit


def target(row, column):
    rb, r = divmod(row, 5)
    cb, c = divmod(column, 5)
    return rb == cb and (GRAPH >> (5 * r + c)) & 1


positive, negative = set(), set()
for rb, cb, r, c in product(range(2), range(2), ROWS, COLUMNS):
    row, column = 5 * rb + r, 5 * cb + c
    (positive if target(row, column) else negative).add(observation(row, column))
assert positive.isdisjoint(negative)


def consistent(ones, zeros):
    """A monotone Boolean function cannot accept a subset of a rejected input."""
    return all(p & ~n for p, n in product(ones, zeros))


@lru_cache(None)
def signatures(private):
    inputs = [observation(*sample) for sample in SAMPLES]
    unary_prices = [price(sum(((x >> j) & 1) << i for i, x in enumerate(inputs)))
                    for j in range(6)]
    assert unary_prices == [1] * 6
    assert price(sum(int(target(*sample)) << i for i, sample in enumerate(SAMPLES))) == 7
    budget = private.bit_count()
    result = []
    for sig in range(128):
        if price(sig) > budget or 2 * price(sig) + 6 - budget < 7:
            continue
        yes = {x & private for i, x in enumerate(inputs) if sig & (1 << i)}
        no = {x & private for i, x in enumerate(inputs) if not sig & (1 << i)}
        if consistent(yes, no):
            result.append((yes, no))
    return result


def compatible(a, b):
    private = a | (b << 6)
    ones, zeros = set(), set()
    for p, n in product(positive, negative):
        if not (p & ~n & ~private):
            ones.add(p & private)
            zeros.add(n & private)
    if not consistent(ones, zeros):
        return False
    for block, mask in enumerate((a, b)):
        shift = 6 * block
        if not any(consistent({p << shift for p in yes}, zeros) and
                   consistent(ones, {n << shift for n in no})
                   for yes, no in signatures(mask)):
            return False
    return True


if __name__ == "__main__":
    pairs = {(a, b) for a, b in product(range(64), repeat=2) if compatible(a, b)}
    mixed = set(product((1, 2, 4), (8, 16, 32)))
    assert pairs == mixed | {(b, a) for a, b in mixed} | {(9, 9)}
    triples = {(a, b, c) for a, b in pairs for x, c in pairs if x == b and (a, c) in pairs}
    assert triples == {(9, 9, 9)}
    # With private mask 9 in each block, freeze h to h(0).
    # Positive cells have zero private input. The output on a negative
    # cell can only decrease; its required value is already zero.
    cells = [(4, 0), (0, 1), (3, 1), (4, 1), (3, 4), (4, 4)]
    outside = (1, 2, 4, 5)  # r3, r4, c1, c4
    words = [observation(*cell) for cell in cells]
    patterns = [sum(((x >> j) & 1) << i for i, j in enumerate(outside)) for x in words]
    assert patterns == [2, 4, 5, 6, 9, 10]
    assert [bool(target(*cell)) for cell in cells] == [False, False, True, True, False, True]
    assert all(not (x & 9) for x, cell in zip(words, cells) if target(*cell))
    print(f"{len(pairs)} ordered pairs; surviving triples: {sorted(triples)}; six cells verified")
