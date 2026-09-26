"""Prove that Spire always finds a copy's record: 58 symbols of σ always leave one candidate.

Spire finds the record of a copy of the calculation at input position p by starting from all
300 paused records and following them through the input symbols before p, dropping those that
cannot read them (spire-at.md, Lemma 2). The true record is never dropped. This program shows
that one record is always left after 58 symbols, from any input position p >= 150; Spire reads
128.

The queen word follows the forty-symbol history graph from column 80 on (the paper, Corollary
19; ../oeis/results/history-40.json). So at every input position p >= 150 the pair (the copy's
record, the forty symbols before p) is reachable from the pair at 150, by the graph's edges and
the records' moves (Section 7.3), and the symbols that follow are a path in the graph. The
program finds every reachable pair, follows every path of the graph from each with the set of
all 300 records, and checks that on every path the set becomes the single true record within 58
symbols. That covers every stretch of σ that Spire can read.

    python3 synchronization.py
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
GENERATED = os.path.join(HERE, '..', 'fast_generator', 'generated')
records = json.load(open(os.path.join(GENERATED, 'paused_records.json')))
history = json.load(open(os.path.join(HERE, '..', 'oeis', 'results', 'history-40.json')))
START = 150    # an input position whose forty symbols come after column 80
READ = 128     # the symbols Spire reads to find a record

COUNT = len(records['states'])
successor = [[-1] * 4 for _ in range(COUNT)]
for a, s, b, _ in records['edges']:
    successor[a][s] = b
MEMORY = history['memory']
graph = {code: [s for s in range(4) if mask >> s & 1] for code, mask in history['vertices']}
def next_vertex(code, s):  # append s, drop the oldest symbol
    return (4 * code + s) % 4 ** MEMORY

# σ_30, σ_31, ...: one copy of the table reading its own output (the paper, Section 7.1).
text = open(os.path.join(GENERATED, 'tables.h')).read()
def define(name):
    return int(re.search(r'#define %s (\d+)' % name, text).group(1))
table = [int(x) for x in re.findall(r'UINT64_C\((\d+)\)', re.search(r'qf_table\[\d+\] = \{(.*?)\};', text, re.S).group(1))]
first = int(re.search(r'#define QF_INITIAL_SYMBOLS UINT64_C\((\d+)\)', text).group(1))
sigma = [(first >> (2 * j)) & 3 for j in range(define('QF_INITIAL_LENGTH'))]
position, read = define('QF_INITIAL_STATE'), 0
while len(sigma) < START:
    byte = sigma[read] | sigma[read + 1] << 2 | sigma[read + 2] << 4 | sigma[read + 3] << 6
    read += 4
    e = table[position + byte]
    position, length, symbols = e & 4095, (e >> 12) & 15, (e >> 16) & 0xFFFFFF
    sigma.extend((symbols >> (2 * j)) & 3 for j in range(length))

# The actual pair at START: the record (following the record graph from record 0, the pause
# before column 48 at input position 30) and the forty symbols before START.
record, window = 0, 0
for i in range(30, START):
    record = successor[record][sigma[i - 30]]
for i in range(START - MEMORY, START):
    window = 4 * window + sigma[i - 30]
assert window in graph, 'the actual window is not a vertex of the graph'

# Every pair reachable from it.
pairs, todo = {(record, window)}, [(record, window)]
while todo:
    r, w = todo.pop()
    for s in graph[w]:
        assert successor[r][s] >= 0, 'the graph allows a symbol the record cannot read'
        pair = (successor[r][s], next_vertex(w, s))
        if pair not in pairs:
            pairs.add(pair)
            todo.append(pair)

# Follow every path from every pair with the candidate set, until every set is one record.
def follow(candidates, s):
    out = 0
    while candidates:
        low = candidates & -candidates
        candidates ^= low
        r = successor[low.bit_length() - 1][s]
        if r >= 0:
            out |= 1 << r
    return out

unsettled = {(r, w, (1 << COUNT) - 1) for r, w in pairs}
depth = 0
while unsettled:
    depth += 1
    if depth > READ:
        sys.exit('synchronization.py: some path leaves more than one record after %d symbols' % READ)
    following = set()
    for r, w, candidates in unsettled:
        for s in graph[w]:
            r2, left = successor[r][s], follow(candidates, s)
            assert left >> r2 & 1, 'the true record was dropped'
            if left != 1 << r2:  # a single true record stays single
                following.add((r2, next_vertex(w, s), left))
    unsettled = following
print('synchronization: %d reachable (record, window) pairs; on every path of the forty-symbol'
      ' graph, one record is left within %d symbols (Spire reads %d)' % (len(pairs), depth, READ))
