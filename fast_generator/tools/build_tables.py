#!/usr/bin/env python3
"""Build the four-symbol transition table of Section 7.3.

Python 3.10 or later, standard library only.  The program

  1. places the first thirty queens directly and computes the bounded
     bounded record of Section 7.2 before column 30 (Sections 6.1 and 7.2);
  2. runs the local rule of Section 7.2 until it needs one more input
     symbol, and explores every input that the history graph allows,
     giving 300 paused records (Section 7.3);
  3. groups the paused records into 82 compatible classes;
  4. combines four input transitions into one table entry, checks every
     four-input path, and packs the entries, their coordinate data, and
     the thirty seed rows into the C header generated/tables.h.

It also writes the finite cases that the C tests replay against the separate
local-rule implementation in tests/local_rule_reference.c, the paused-record
graph, and the construction counts.  Every check is an assertion, so run it
without -O.

  python3 tools/build_tables.py            # write generated/
  python3 tools/build_tables.py --check    # rebuild in memory and compare

The history graph is read from ../verification/history.json (Section 4.3).
It is used only to decide which inputs to explore; the executable never
reads it.
"""
from __future__ import annotations

import argparse
from collections import deque
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_HISTORY = ROOT.parent / 'verification' / 'history.json'

MEMORY = 12   # length of a history-graph vertex
START = 30    # the local calculation starts before column 30
BLOCK = 4     # input symbols per table lookup: four two-bit symbols = one byte

# A bounded record (Section 7.2) is the tuple
# (w, z, R, D, A, past, Q):
#   w, z     integers, as in Section 4;
#   R, D, A  the offset sets (12), stored as bit masks (bit a <=> a in set);
#   past     the upper-column bits u_{m-4} u_{m-3} u_{m-2} u_{m-1}, with the
#            newest bit u_{m-1} in bit 0;
#   Q        the queue sigma_m sigma_{m+1} ..., a tuple of symbols 2u + b.
# A symbol-level output of one queen placement is the integer
#   symbol | mu << 2 | r << 5,
# where symbol = sigma_n, mu is the row advance and r the lower offset
# (zero for an upper queen).


# --------------------------------------------------------------- the seed

def greedy_prefix(length: int) -> list[int]:
    """Rows q_0, ..., q_{length-1}, directly from the greedy rule."""
    rows, diagonals, antidiagonals, queens = set(), set(), set(), []
    for n in range(length):
        y = 0
        while y in rows or y - n in diagonals or y + n in antidiagonals:
            y += 1
        queens.append(y)
        rows.add(y)
        diagonals.add(y - n)
        antidiagonals.add(y + n)
    return queens


def queen_word(queens: list[int]) -> list[int | None]:
    """sigma_i = 2 u_i + b_i for 1 <= i < len(queens) (Section 4.2).

    Index 0 holds None, so that sigma[i] is the ith symbol.
    """
    upper_rows = {y for x, y in enumerate(queens) if y > x}
    return [None] + [2 * int(queens[i] > i) + int(i in upper_rows)
                     for i in range(1, len(queens))]


def seed_record(queens: list[int]):
    """The bounded record before column 30 and the counters of the seed.

    Returns (record, m, upper_count, kappa, sigma), where m is the least
    unused row, upper_count = U(29) is the number of upper queens among the
    thirty seed queens, and kappa = U(m - 1).
    """
    n = len(queens)
    sigma = queen_word(queens)
    lower = [(x, y) for x, y in enumerate(queens) if y < x]
    used_rows = set(queens)
    m = next(y for y in range(1, n + 1) if y not in used_rows)
    magnitudes = {x - y for x, y in lower}
    d = next(e for e in range(1, n + 1) if e not in magnitudes)
    kappa = sum(int(queens[c] > c) for c in range(1, m))
    upper = [int(q > i) for i, q in enumerate(queens)]
    mask = lambda offsets: sum(1 << a for a in offsets)
    record = (
        n - m - d,                                             # w
        n - m - kappa,                                         # z
        mask(y - m for x, y in lower if y >= m),               # R
        mask(x - y - d for x, y in lower if x - y >= d),       # D
        mask(x + y - n - m for x, y in lower if x + y >= n + m),  # A
        sum(upper[m - 1 - i] << i for i in range(4)),          # past
        tuple(sigma[m:n]),                                     # Q
    )
    return record, m, sum(upper), kappa, sigma


# ------------------------------------------------------- the history graph

def encode(word) -> int:
    """Base-four code of a word, newest symbol in the least significant digit."""
    code = 0
    for symbol in word:
        code = 4 * code + symbol
    return code


def load_history_graph(path: Path) -> dict[int, tuple[int, ...]]:
    """Return {vertex code: allowed next symbols} from history.json.

    Each vertex is [h, mask]: h encodes a twelve-symbol word as in encode(),
    and bit s of mask permits the edge labelled s.
    """
    data = json.loads(path.read_text())
    assert data['memory'] == MEMORY
    graph = {}
    for code, mask in data['vertices']:
        assert 0 <= code < 4 ** MEMORY and 0 <= mask < 16 and code not in graph
        graph[code] = tuple(s for s in range(4) if mask >> s & 1)
    for code, symbols in graph.items():
        for s in symbols:
            assert next_vertex(code, s) in graph, 'an edge leaves the graph'
    return graph


def next_vertex(code: int, symbol: int) -> int:
    """The edge W --s--> last(Ws): append s and drop the oldest symbol."""
    return ((code << 2) | symbol) & (4 ** MEMORY - 1)


def check_seed_word(graph, sigma) -> int:
    """Check that sigma_1 ... sigma_29 follows the graph; return its last window."""
    for t in range(MEMORY, START - 1):
        window = encode(sigma[t - MEMORY + 1:t + 1])
        assert sigma[t + 1] in graph[window], f'no edge for sigma_{t + 1}'
    last = encode(sigma[START - MEMORY:START])
    assert last in graph
    return last


# -------------------------------------------------------- the local rule

class LocalRule:
    """The bounded local calculation of Sections 4.5 and 7.2.

    step() places one queen, or reports that it needs one more input symbol
    at the end of Q.  Every call is recorded in self.cases; these are the
    local cases replayed by tests/check_local_steps.c.
    """

    def __init__(self):
        self.cases = {}

    def step(self, s):
        """One complete step from record s: (output, successor), or None."""
        w, z, R, D, A, past, Q = s
        # Section 7.2: first extend Q to length max(1, z, w + 1).
        if len(Q) < max(1, z, w + 1):
            self.cases[s] = None
            return None
        # Upper attacks and the new row bit, from the four past upper columns
        # (h = -1, ..., -4) and then from Q (h = 0, 1, ...).  count is
        # |Gamma(h)| of (15).  An upper queen in column m+h lies in row n
        # exactly when h + Gamma(h) = z (Section 7.2), and attacks the candidate at
        # offset r along its antidiagonal when 2h + Gamma(h) = z + r (18).
        blocked, row_bit, count = R | A, 0, 0
        for distance in range(1, 5):
            if (past >> (distance - 1)) & 1:
                row_bit |= int(-distance - count == z)
                r = -2 * distance - count - z
                if 0 <= r <= w:
                    blocked |= 1 << r
                count += 1
        count = 0
        limit = min(len(Q), max(0, z, (z + w) // 2 + 1))
        for h in range(limit):
            if Q[h] & 2:
                count += 1
                row_bit |= int(h + count == z)
                r = 2 * h + count - z
                if 0 <= r <= w:
                    blocked |= 1 << r
        # Choose the lowest candidate free of all five attacks (Section 4.5):
        # R and A and the antidiagonal tests are in `blocked`, D is tested
        # at w - r, and the upper-row bit is the low bit of Q[r].
        chosen = next((r for r in range(w + 1)
                       if not (blocked >> r) & 1
                       and not (D >> (w - r)) & 1 and not Q[r] & 1), None)
        symbol = 2 * (chosen is None) + row_bit
        if chosen is not None:
            R |= 1 << chosen
            D |= 1 << (w - chosen)
            A |= 1 << chosen
        # The advances nu (diagonal) and mu (row).  The row search may need
        # input beyond the end of Q.
        nu = 0
        while (D >> nu) & 1:
            nu += 1
        mu = 0
        while True:
            if mu >= len(Q):
                self.cases[s] = None
                return None
            if not (R >> mu) & 1 and not Q[mu] & 1:
                break
            mu += 1
        # The record update of Section 4.5; the upper bits of the symbols leaving Q enter
        # the four stored past bits.
        upper_advance = 0
        for value in Q[:mu]:
            upper = value >> 1
            upper_advance += upper
            past = ((past << 1) | upper) & 15
        new = (w + 1 - mu - nu, z + 1 - mu - upper_advance,
               R >> mu, D >> nu, A >> (mu + 1), past, Q[mu:])
        nw, nz, nr, nd, na, _, nq = new
        assert -4 <= nw <= 4 and -4 <= nz <= 5 and -4 <= nz - nw <= 3
        assert nr < 32 and not nr & 1 and nd < 32 and not nd & 1 and na < 16
        assert 1 <= len(nq) <= 11 and not nq[0] & 1 and mu <= 6
        output = symbol | (mu << 2) | ((chosen or 0) << 5)
        self.cases[s] = (output, new)
        return output, new

    def run_until_input(self, s):
        """Run complete steps until one more input symbol is needed.

        Returns the paused record and the tuple of outputs produced.
        """
        outputs = []
        while (result := self.step(s)) is not None:
            output, s = result
            outputs.append(output)
            assert len(outputs) <= 32
        return s, tuple(outputs)


def with_input(s, symbols):
    """Record s with the given input symbols appended to Q."""
    return s[:-1] + (s[-1] + tuple(symbols),)


# ---------------------------------------------- paused records (Sec. 7.3)

def explore_paused_records(rule: LocalRule, graph, seed, history):
    """All paused records reachable when inputs follow the history graph.

    Each paused record is paired with the twelve symbols ending at the right
    end of Q, a history-graph vertex.  Every outgoing edge is followed.
    Returns (records, edges, initial_output, counts), where records[i] is
    the ith paused record and edges[i, s] = (j, outputs) says that input s
    at record i produces the outputs and pauses at record j.
    """
    first, initial_output = rule.run_until_input(seed)
    index = {first: 0}
    seen = {(first, history)}
    todo = deque(seen)
    edges = {}
    pair_edges = 0
    while todo:
        s, h = todo.popleft()
        assert graph[h]
        for symbol in graph[h]:
            target, outputs = rule.run_until_input(with_input(s, [symbol]))
            index.setdefault(target, len(index))
            key, edge = (index[s], symbol), (index[target], outputs)
            # The calculation reads only the record and the input symbol.
            assert key not in edges or edges[key] == edge
            edges[key] = edge
            pair_edges += 1
            pair = (target, next_vertex(h, symbol))
            if pair not in seen:
                seen.add(pair)
                todo.append(pair)
    records = list(index)
    assert len(records) == 300 and len(seen) == 2489
    # Needed for the lead inequality of Section 7.4: z - |Q| >= -4 at every paused record.
    assert min(s[1] - len(s[-1]) for s in records) >= -4
    counts = {'history_record_pairs': len(seen), 'history_record_pair_edges': pair_edges,
              'paused_records': len(records), 'one_input_edges': len(edges),
              'initial_output_length': len(initial_output),
              'max_one_input_output': max(len(o) for _, o in edges.values()),
              'min_paused_z_minus_queue_length': min(s[1] - len(s[-1]) for s in records)}
    return records, edges, initial_output, counts


def merge_records(count: int, edges):
    """Group paused records into compatible classes (Section 7.3).

    Two records may share a class when, on every input defined at both,
    they give identical output lists and successors that can also share a
    class.  An input undefined at a record imposes no condition.  Records
    are merged greedily; each tentative merge is kept only if all of the
    conditions it implies can be met.
    Returns (class of each record, number of classes, class-level edges).
    """
    parent = list(range(count))
    rows = [{} for _ in range(count)]
    for (i, symbol), edge in edges.items():
        rows[i][symbol] = edge
    for first in range(count):
        for second in range(first + 1, count):
            if parent[first] != first or parent[second] != second:
                continue
            p = parent.copy()
            e = [row.copy() for row in rows]

            def root(i):
                while p[i] != i:
                    i = p[i]
                return i
            pending = [(first, second)]
            compatible = True
            while pending and compatible:
                a, b = map(root, pending.pop())
                if a == b:
                    continue
                if a > b:
                    a, b = b, a
                for symbol, (target, output) in e[b].items():
                    if symbol in e[a]:
                        target2, output2 = e[a][symbol]
                        if output != output2:
                            compatible = False
                            break
                        pending.append((target, target2))
                    else:
                        e[a][symbol] = (target, output)
                p[b], e[b] = a, {}
            if compatible:
                parent, rows = p, e

    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    representatives = [i for i in range(count) if parent[i] == i]
    ids = {r: i for i, r in enumerate(representatives)}
    mapping = [ids[root(i)] for i in range(count)]
    # Check every defined transition against the classes.
    class_edges = {}
    for (i, symbol), (j, output) in edges.items():
        key, edge = (mapping[i], symbol), (mapping[j], output)
        assert key not in class_edges or class_edges[key] == edge
        class_edges[key] = edge
    assert len(representatives) == 82
    return mapping, len(representatives), class_edges


def four_input_paths(count: int, edges):
    """Every path of four input transitions on the 300-record graph.

    Yields (start, byte, end, outputs) in a fixed order; byte packs the
    four input symbols, the first in the low two bits.
    """
    for start in range(count):
        paths = [(start, 0, ())]
        for b in range(BLOCK):
            following = []
            for j, byte, outputs in paths:
                for symbol in range(4):
                    if (j, symbol) in edges:
                        target, more = edges[j, symbol]
                        following.append((target, byte | (symbol << (2 * b)),
                                          outputs + more))
            paths = following
        for end, byte, outputs in paths:
            yield start, byte, end, outputs


def pack_record(s):
    """The record in the four-field format of tests/local_rule_reference.c."""
    w, z, R, D, A, past, Q = s
    queue = sum(symbol << (2 * i) for i, symbol in enumerate(Q))
    return (queue, R | (D << 5) | (A << 10), past | (len(Q) << 4),
            (w + 4) | ((z + 4) << 4))


# ------------------------------------------------------------ the table

def coordinate_data(outputs):
    """The coordinate data of one table entry, from the coordinate formula of Section 7.3.

    Returns [length, row advance, upper advance, code_0, code_1, ...].  The
    code of a lower queen is its offset from the block's row reference m_0;
    the code of an upper queen is 128 plus its offset from n_0 + U_0.
    """
    mu_total = u_total = 0
    codes = []
    for j, output in enumerate(outputs):
        if output & 2:
            u_total += 1
            code = 128 + j + u_total
        else:
            code = mu_total + (output >> 5)
        assert 0 <= code <= 255
        codes.append(code)
        mu_total += (output >> 2) & 7
    assert mu_total <= 255 and u_total <= 255
    return [len(outputs), mu_total, u_total, *codes]


def build_table(records, edges, mapping, class_count, initial_output, queens,
                m, upper_count):
    """Pack the table (Section 7.3) and return (header text, block cases, counts)."""
    paths = list(four_input_paths(len(records), edges))
    # The class and the input byte must determine a single entry.
    rows = [{} for _ in range(class_count)]
    for start, byte, end, outputs in paths:
        entry = (mapping[end], outputs)
        row = rows[mapping[start]]
        assert byte not in row or row[byte] == entry
        row[byte] = entry

    # Coordinate data, shared by entries with the same output list.  The
    # data for the eighteen initial outputs come last.
    data, data_offset = [], {}
    for row in rows:
        for _, outputs in row.values():
            data_offset.setdefault(outputs, None)
    data_offset.setdefault(initial_output, None)
    for outputs in data_offset:
        data_offset[outputs] = len(data)
        data.extend(coordinate_data(outputs))

    # Each class gets a base offset into one array; the entry for input byte
    # a lives at base + a.  Classes with the most entries are placed first,
    # each at the least base where none of its slots is taken.
    occupied = 0
    bases = [0] * class_count
    for i in sorted(range(class_count), key=lambda i: (-len(rows[i]), i)):
        row_mask = sum(1 << byte for byte in rows[i])
        base = 0
        while (row_mask << base) & occupied:
            base += 1
        bases[i] = base
        occupied |= row_mask << base
    slot_count = occupied.bit_length()

    # 64-bit entry layout, low to high: successor base offset, number of
    # output symbols, the output symbols (two bits each), and the offset
    # of the coordinate data.
    base_bits = max(bases).bit_length()
    max_output = max(len(outputs) for row in rows for _, outputs in row.values())
    length_bits = max_output.bit_length()
    symbol_bits = 2 * max_output
    data_bits = (len(data) - 1).bit_length()
    assert base_bits + length_bits + symbol_bits + data_bits <= 64
    length_shift = base_bits
    symbol_shift = length_shift + length_bits
    data_shift = symbol_shift + symbol_bits

    entries, owners = [0] * slot_count, [65535] * slot_count
    for i, row in enumerate(rows):
        for byte, (j, outputs) in row.items():
            index = bases[i] + byte
            assert owners[index] == 65535, 'two entries share a slot'
            owners[index] = bases[i]
            symbols = sum((output & 3) << (2 * k) for k, output in enumerate(outputs))
            entries[index] = (bases[j] | len(outputs) << length_shift
                              | symbols << symbol_shift
                              | data_offset[outputs] << data_shift)

    # Check every four-input path against the packed table, and record it
    # for tests/check_table_paths.c.
    block_cases = []
    for start, byte, end, outputs in paths:
        index = bases[mapping[start]] + byte
        entry = entries[index]
        assert owners[index] == bases[mapping[start]]
        assert entry & ((1 << base_bits) - 1) == bases[mapping[end]]
        assert (entry >> length_shift) & ((1 << length_bits) - 1) == len(outputs)
        assert all((entry >> (symbol_shift + 2 * k)) & 3 == output & 3
                   for k, output in enumerate(outputs))
        offset = entry >> data_shift
        assert data[offset:offset + 3 + len(outputs)] == coordinate_data(outputs)
        source = records[start]
        prepared = with_input(source, [(byte >> (2 * k)) & 3 for k in range(BLOCK)])
        numbers = [index, bases[mapping[start]], bases[mapping[end]],
                   *pack_record(prepared), len(outputs), *outputs,
                   *pack_record(records[end])]
        block_cases.append(' '.join(map(str, numbers)))

    lines = ['/* Generated by tools/build_tables.py; do not edit. */',
             '#ifndef QF_TABLES_H', '#define QF_TABLES_H', '#include <stdint.h>']
    # QF_COMPACT 0: the input byte is added directly to the base offset.
    # QF_SEPARATE_PACKET 0: each entry holds its own coordinate-data offset.
    macros = {'QF_BLOCK': BLOCK, 'QF_COMPACT': 0, 'QF_SEPARATE_PACKET': 0,
              'QF_STATE_COUNT': class_count, 'QF_INITIAL_STATE': bases[mapping[0]],
              'QF_INITIAL_PACKET': data_offset[initial_output],
              'QF_STATE_MASK': (1 << base_bits) - 1,
              'QF_LENGTH_SHIFT': length_shift, 'QF_LENGTH_MASK': (1 << length_bits) - 1,
              'QF_SYMBOL_SHIFT': symbol_shift, 'QF_PACKET_SHIFT': data_shift,
              'QF_INITIAL_M': m, 'QF_INITIAL_UPPER': upper_count,
              'QF_INITIAL_LENGTH': len(initial_output), 'QF_SLOT_COUNT': slot_count}
    for key, value in macros.items():
        lines.append(f'#define {key} {value}u')
    lines.append(f'#define QF_SYMBOL_MASK UINT64_C({(1 << symbol_bits) - 1})')
    initial_bits = sum((output & 3) << (2 * i) for i, output in enumerate(initial_output))
    lines.append(f'#define QF_INITIAL_SYMBOLS UINT64_C({initial_bits})')

    def array(ctype, name, values, width=12):
        lines.append(f'static const {ctype} {name}[{len(values)}] = {{')
        for i in range(0, len(values), width):
            render = [f'UINT64_C({v})' if ctype == 'uint64_t' else str(v)
                      for v in values[i:i + width]]
            lines.append('    ' + ','.join(render) + ',')
        lines.append('};')
    array('uint64_t', 'qf_table', entries, 6)
    array('uint8_t', 'qf_packets', data, 20)
    array('uint8_t', 'qf_seed_queens', queens, 15)
    # Assertion builds check that each lookup lands in its own class's row.
    lines.append('#ifndef NDEBUG')
    array('uint32_t', 'qf_owners', owners)
    lines.extend(['#endif', '#endif', ''])

    counts = {'four_input_paths': len(paths),
              'table_entries': sum(map(len, rows)), 'table_slots': slot_count,
              'distinct_output_lists': len(data_offset),
              'coordinate_data_bytes': len(data),
              'fixed_data_bytes': 8 * slot_count + len(data) + len(queens),
              'assertion_build_owner_bytes': 4 * slot_count,
              'min_entry_output': min(len(o) for row in rows for _, o in row.values()),
              'max_entry_output': max_output}
    return '\n'.join(lines), block_cases, counts


# ------------------------------------------------------------- artifacts

def build(history_path: Path) -> dict[str, str]:
    """Return {file name in generated/: contents}."""
    graph = load_history_graph(history_path)
    queens = greedy_prefix(START)
    seed, m, upper_count, kappa, sigma = seed_record(queens)
    # The starting values of Section 7.2.
    assert seed == (0, -1, 0, 0b10, 0, 0b1111, (0, 0, 3, 2, 2, 3, 0, 1, 2, 1, 2))
    assert (m, upper_count, kappa) == (19, 18, 12)
    history = check_seed_word(graph, sigma)

    rule = LocalRule()
    records, edges, initial_output, counts = explore_paused_records(
        rule, graph, seed, history)
    # The first pause comes after columns 30..47, with m = 29, kappa = 17.
    pause_m = m + sum((output >> 2) & 7 for output in initial_output)
    pause_kappa = sum(int(y > x) for x, y in enumerate(queens[:pause_m]))
    assert (len(initial_output), pause_m, pause_kappa) == (18, 29, 17)

    mapping, class_count, class_edges = merge_records(len(records), edges)
    header, block_cases, table_counts = build_table(
        records, edges, mapping, class_count, initial_output, queens, m, upper_count)

    local_cases = []
    for s, result in sorted(rule.cases.items()):
        if result is None:
            local_cases.append(' '.join(map(str, [0, *pack_record(s)])))
        else:
            output, target = result
            local_cases.append(' '.join(map(str, [1, *pack_record(s), output,
                                                  *pack_record(target)])))
    demands = sum(result is None for result in rule.cases.values())
    counts.update(table_counts)
    counts.update({'classes': class_count, 'class_one_input_edges': len(class_edges),
                   'seed_m': m, 'seed_kappa': kappa, 'seed_upper_count': upper_count,
                   'first_pause_n': START + len(initial_output),
                   'first_pause_m': pause_m, 'first_pause_kappa': pause_kappa,
                   'local_cases': len(local_cases), 'local_input_demands': demands,
                   'local_completed_steps': len(local_cases) - demands})
    paused = {'state_format': ['w', 'z', 'R', 'D', 'A', 'past4_newest_low', 'Q'],
              'states': records, 'mapping_to_82_classes': mapping,
              'initial_output': initial_output,
              'edges': [[i, s, j, list(out)] for (i, s), (j, out) in sorted(edges.items())]}
    return {
        'tables.h': header,
        'local_cases.txt': '\n'.join(local_cases) + '\n',
        'block_cases.txt': '\n'.join(block_cases) + '\n',
        'paused_records.json': json.dumps(paused, separators=(',', ':')) + '\n',
        'construction_counts.json': json.dumps(counts, indent=2, sort_keys=True) + '\n',
    }


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--check', action='store_true',
                        help='compare with the files in the output directory instead of writing')
    parser.add_argument('--history', type=Path, default=DEFAULT_HISTORY)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'generated')
    args = parser.parse_args()
    started = time.perf_counter()
    files = build(args.history)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        destination = args.output_dir / name
        if args.check:
            assert destination.read_text() == text, f'{destination} differs'
        else:
            destination.write_text(text, newline='\n')
    print(json.dumps({'checked' if args.check else 'written': sorted(files),
                      'seconds': round(time.perf_counter() - started, 3)}, indent=2))


if __name__ == '__main__':
    main()
