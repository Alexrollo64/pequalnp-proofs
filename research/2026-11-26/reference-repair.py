"""Exhaustive one-deletion, one-rewrite search around the 17-gate reference."""
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path
import json
import re

N = 20
FULL = (1 << 100) - 1
RAW = [sum(1 << (10*r+c) for r in range(10) for c in range(10)
           if wire in (r, 10+c)) for wire in range(N)]
TARGET = sum(1 << (10*r+c) for r in range(10) for c in range(10)
             if r//5 == c//5 and (31917056 >> (5*(r%5)+c%5)) & 1)


def read_reference():
    text = Path(__file__).with_name("DisjointCopies.lean").read_text()
    block = text.split("def twoCircuit : Circuit :=", 1)[1].split("theorem", 1)[0]
    gates = [(op, int(a), int(b)) for op, a, b in
             re.findall(r"⟨\.(and|or), \[(\d+), (\d+)\]⟩", block)]
    assert len(gates) == 17 and "], 36⟩" in block
    return gates


def evaluate(gates, output, force=None):
    w = RAW.copy()
    for wire, (op, a, b) in enumerate(gates, N):
        value = w[a] & w[b] if op == "and" else w[a] | w[b]
        w.append(force[1] if force and force[0] == wire else value)
    return w[output], w


def delete(gates, removed, alias):
    def adjust(w):
        return alias if w == removed else w - int(w > removed)
    return ([(op, adjust(a), adjust(b)) for w, (op, a, b) in enumerate(gates, N)
             if w != removed], adjust(36))


def scan():
    reference = read_reference()
    assert evaluate(reference, 36)[0] == TARGET
    hist = Counter()
    near = {}
    for removed in range(20, 37):
        for alias in range(removed):
            gates, output = delete(reference, removed, alias)
            _, w = evaluate(gates, output)
            for gate in range(N, N+16):
                low = evaluate(gates, output, (gate, 0))[0]
                high = evaluate(gates, output, (gate, FULL))[0]
                assert low & ~high == 0
                # Per configuration, the suffix is a unary monotone Boolean function.
                # Its two cofactors determine its output for every replacement.
                for a, b in combinations_with_replacement(range(gate), 2):
                    for op, value in (("and", w[a] & w[b]), ("or", w[a] | w[b])):
                        diff = (low | (high & value)) ^ TARGET
                        count = diff.bit_count()
                        hist[count] += 1
                        if count <= 1 and diff not in near:
                            edited = gates.copy()
                            edited[gate-N] = (op, a, b)
                            assert evaluate(edited, output)[0] ^ TARGET == diff
                            near[diff] = (edited, output)
    return hist, near


if __name__ == "__main__":
    hist, near = scan()
    print("edit descriptions:", sum(hist.values()), "minimum errors:", min(hist))
    print("one-error descriptions:", hist[1])
    print("reachable single-error cells:", [divmod(d.bit_length()-1,10) for d in sorted(near) if d])
    print(json.dumps({str(d): x for d, x in sorted(near.items())}))
