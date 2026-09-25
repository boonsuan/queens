"""Occurrence witnesses from the actual greedy queens (Section 6.5, Appendix A).

    python witnesses.py

The graphs give upper bounds only: a path in a graph need not occur in the
actual sequence. Attainment, nonfaithfulness, and the columns before the
graphs apply are settled here, from actual queens computed by two separate
programs:

  * bitboard_queens applies the defining greedy rule with bit masks of
    attacked rows, diagonals, and antidiagonals;
  * upper_queen_generator uses the lemma of Section 2 (the kth upper queen lies on the kth
    upper diagonal) and searches for a lower queen only between the least
    unused row m and the row n - d allowed by the least unused lower-diagonal
    magnitude d. It is fast enough for a million queens.

The first 200000 queens of the two programs are compared. Columns are
zero-based; indices of OEIS terms are one-based. As in the OEIS entries, the
origin counts as an upper column.

Column runs and gaps (the first 20000 queens):
  * every value in the table of the corollary "Column runs and gaps" occurs, and no other;
  * the origin creates no run of four lower or six upper columns;
  * for c = 1, 2, 3 the maximal runs of c's in A275885 have exactly the
    lengths L_c computed by runs_and_gaps.py;
  * every maximal run of equal terms of A275885 that the run graph does not
    cover (see initial_runs) has a length in L_c. These runs end by column 95.

Return words and 4s (the first 1000000 queens, 618034 terms of A275888):
  * every return word to 3 in the catalogue occurs, the last by index 108015;
  * every word and every successor pair in the prefix is permitted by the
    forty-symbol graph (return_words.py); this includes the words that
    begin before the graph applies;
  * each of the 93 words with several permitted successors has two
    different actual successors, all found by index 573517;
  * the gap factors 11111, 2222, 33, 44, and 3213 never occur, also not at
    the origin;
  * the first 4 is at index 3073 (columns 4969 to 4973), after the start
    before column 80, so four_gaps.py covers every pair of 4s;
  * consecutive 4s at indices 83418 and 83489 attain the distance 71.

Output: results/witnesses.json, with the first occurrence of every value,
word, and successor pair, and results/a275888-prefix.txt, the first 618034
terms of A275888 as one line of digits.
"""
from __future__ import annotations

import json

import graphs
from four_gaps import EXPECTED_FILL
from graphs import RESULTS, require
from return_words import read_catalogue, return_words
from runs_and_gaps import EXPECTED_RUN_LENGTHS, FORBIDDEN_GAP_FACTORS

GRAPH_START = 80            # the forty-symbol graph applies from the state before this column
EXPECTED_VALUES = {'A275885': {1, 2, 3}, 'A275886': {1, 2, 3, 4, 5},
                   'A275887': {1, 2, 3, 4, 5, 6, 7, 8, 9, 11}, 'A275888': {1, 2, 3, 4},
                   'A275889': {1, 2, 3, 4, 5, 6}}
# First indices of the values of A275887, as recorded in that entry.
A275887_FIRST = {1: 7, 2: 1, 3: 29, 4: 14, 5: 4, 6: 22, 7: 64, 8: 178, 9: 534, 11: 230}


# ------------------------------------------------------------ two generators

def bitboard_queens(count: int) -> list[int]:
    """q_0, ..., q_{count-1} by the defining rule, using bit masks.

    Before column n, bit y of `rows` is set when row y holds a queen, bit y
    of `diagonals` when the square (n, y) shares a diagonal y - x with an
    earlier queen, and bit y of `antidiagonals` when it shares an
    antidiagonal x + y. Moving to the next column shifts the diagonals up
    and the antidiagonals down. The queen takes the lowest clear bit.
    """
    rows = diagonals = antidiagonals = 0
    q = []
    for n in range(count):
        attacked = rows | diagonals | antidiagonals
        bit = (attacked + 1) & ~attacked          # the lowest clear bit
        q.append(bit.bit_length() - 1)
        rows |= bit
        diagonals = (diagonals | bit) << 1
        antidiagonals = (antidiagonals | bit) >> 1
    return q


def upper_queen_generator(count: int) -> tuple[list[int], list[int]]:
    """q_0, ..., q_{count-1} and the upper columns, using the lemma of Section 2.

    In column n, every row below the least unused row m is taken, and every
    lower diagonal of magnitude below the least unused magnitude d is taken
    (the origin takes magnitude 0), so a lower queen lies in a row between m
    and n - d. If no such row is free, the queen is the (k+1)st upper queen,
    in row n + k + 1 by the lemma of Section 2.
    """
    # Room for every row, magnitude, and antidiagonal used: an upper row
    # n + k is below 2 count. Indexing past the end would stop with an error.
    rows = bytearray(2 * count)
    magnitudes = bytearray(count)
    antidiagonals = bytearray(3 * count)
    q, uppers = [0], [0]                        # the origin counts as upper here
    rows[0] = antidiagonals[0] = 1
    m, d, k = 1, 1, 0
    for n in range(1, count):
        y = m
        while y <= n - d and (rows[y] or magnitudes[n - y] or antidiagonals[n + y]):
            y += 1
        if y <= n - d:                          # a lower queen
            magnitudes[n - y] = 1
            while magnitudes[d]:
                d += 1
        else:                                   # an upper queen, by the lemma of Section 2
            k += 1
            y = n + k
            uppers.append(n)
        require(not rows[y] and not antidiagonals[n + y], f'column {n}: row {y} is attacked')
        rows[y] = antidiagonals[n + y] = 1
        q.append(y)
        while rows[m]:
            m += 1
    return q, uppers


# ------------------------------------------------------------ sequences

def maximal_runs(values: list) -> list[tuple]:
    """(value, first index, last index) of each maximal run of equal
    values, zero-based; the last run is omitted, since it may continue."""
    runs, start = [], 0
    for i in range(1, len(values)):
        if values[i] != values[start]:
            runs.append((values[start], start, i - 1))
            start = i
    return runs


def first_indices(values: list) -> dict:
    """The one-based index of the first occurrence of each value."""
    first = {}
    for i, v in enumerate(values, 1):
        first.setdefault(v, i)
    return dict(sorted(first.items()))


def column_sequences(q: list[int]) -> dict:
    """The five OEIS sequences of the corollary "Column runs and gaps", from the columns 0..len(q)-1."""
    u = [1] + [int(q[n] > n) for n in range(1, len(q))]     # the origin counts as upper
    uppers = [n for n, bit in enumerate(u) if bit]
    lowers = [n for n, bit in enumerate(u) if not bit]
    runs = maximal_runs(u)
    lower_runs = [e - s + 1 for bit, s, e in runs if bit == 0]
    return {'u': u, 'uppers': uppers,
            'A275885': lower_runs,
            'A275886': [e - s + 1 for bit, s, e in runs if bit == 1],
            'A275887': [e - s + 1 for _, s, e in maximal_runs(lower_runs)],
            'A275888': [b - a for a, b in zip(uppers, uppers[1:])],
            'A275889': [b - a for a, b in zip(lowers, lowers[1:])]}


# ------------------------------------------------------------ the corollary "Column runs and gaps"

def initial_runs(g: list[int], uppers: list[int]) -> tuple[list[dict], dict]:
    """Check the maximal runs of equal terms of A275885 against L_c.

    Obtain A275885 from g = A275888 as in the proof of the corollary "Column runs and gaps": delete
    the 1s and replace each other term k by k - 1. Term i of A275885 is the
    lower run ending just before upper column y_i. In the run graph, it is
    the edge from the state after column y_{i-1} to the state after column
    y_i. The actual walk visits the states after every column >= 79. So a
    maximal run of terms s..e, whose preceding unequal term s-1 is an edge
    from the state after y_{s-2}, is covered by the graph when s >= 2 and
    y_{s-2} >= 79. The other runs are the initial runs; for them the length
    is checked here directly, which needs the columns up to y_{e+1}.

    Returns the initial runs and, for each c and each length, the first run.
    """
    events = [(k - 1, uppers[n]) for n, k in enumerate(g, 1) if k > 1]   # (term, y)
    r = [term for term, _ in events]
    initial, first = [], {c: {} for c in EXPECTED_RUN_LENGTHS}
    for index, (c, s, e) in enumerate(maximal_runs(r), 1):
        length = e - s + 1
        record = {'A275887 index': index, 'repeated term': c, 'length': length,
                  'A275885 indices': [s + 1, e + 1], 'last column needed': events[e + 1][1]}
        require(length in EXPECTED_RUN_LENGTHS[c], f'a maximal run of {length} {c}s occurs')
        first[c].setdefault(length, record)
        if s < 2 or events[s - 2][1] < GRAPH_START - 1:
            initial.append(record)
    return initial, first


def check_column_sequences(q: list[int]) -> tuple[dict, list[str]]:
    seq = column_sequences(q)
    columns = ''.join(map(str, seq['u']))
    require('0000' not in columns and '111111' not in columns,
            'four lower or six upper consecutive columns occur')
    values = {name: first_indices(seq[name]) for name in EXPECTED_VALUES}
    for name, expected in EXPECTED_VALUES.items():
        require(set(values[name]) == expected, f'{name} takes the values {sorted(values[name])}')
    require({k: values['A275887'][k] for k in A275887_FIRST} == A275887_FIRST,
            'the first occurrences in A275887 differ from those recorded in the entry')
    derived = [k - 1 for k in seq['A275888'] if k > 1]
    require(derived[:len(seq['A275885'])] == seq['A275885'],
            'A275885 differs from A275888 with 1s deleted and 1 subtracted')
    initial, first = initial_runs(seq['A275888'], seq['uppers'])
    for c, lengths in EXPECTED_RUN_LENGTHS.items():
        require(sorted(first[c]) == lengths, f'the maximal runs of {c}s have lengths {sorted(first[c])}')
    last_column = max(run['last column needed'] for run in initial)
    require(last_column < len(q), 'the initial runs are not complete in the prefix')
    result = {'columns': len(q), 'first indices of each value': values,
              'first maximal run of each length, by repeated term': first,
              'initial runs of A275887, checked directly': initial}
    lines = [f'first {len(q)} queens: every value of the corollary "Column runs and gaps" occurs, and no other',
             'A275887 first indices ' + str(values['A275887']),
             'the maximal runs of c in A275885 attain every length in L_c, for c = 1, 2, 3',
             f'{len(initial)} initial runs of A275887 are checked directly, through column {last_column}']
    return result, lines


# ------------------------------------------------------------ return words and 4s

def check_gap_prefix(g: list[int], uppers: list[int]) -> tuple[dict, list[str]]:
    text = ''.join(map(str, g))
    require(max(g) == 4 and g[:10] == [1, 1, 3, 1, 1, 1, 3, 2, 2, 1], 'unexpected terms of A275888')
    for factor in FORBIDDEN_GAP_FACTORS:
        require(factor not in text, f'the factor {factor} occurs')
    # Cut after each 3. Record the first occurrence of each word, and of each
    # successor pair by the index of its last term.
    catalogue = read_catalogue()
    successors = return_words(graphs.forty_symbol_graph())
    words, start = [], 0                                       # (word, start, end), one-based
    for n, k in enumerate(g, 1):
        if k == 3:
            words.append((text[start:n], start + 1, n))
            start = n
    first_word, first_pair = {}, {}
    for word, s, e in words:
        require(word in catalogue, f'the return word {word} is not in the catalogue')
        first_word.setdefault(word, [s, e])
    for (word, _, _), (following, _, e) in zip(words, words[1:]):
        require(following in successors[word], f'{word} followed by {following} is not permitted')
        first_pair.setdefault(word, {}).setdefault(following, e)
    require(set(first_word) == catalogue, 'a catalogue word does not occur')
    last_word = max(first_word, key=lambda w: first_word[w][1])
    require(first_word[last_word] == [108002, 108015], 'the last first occurrence does not end at 108015')
    several = {w for w in catalogue if len(successors[w]) > 1}
    require(len(several) == 93, 'expected 93 words with several permitted successors')
    two_successors = {}
    for word in several:
        found = sorted(first_pair.get(word, {}).items(), key=lambda item: item[1])
        require(len(found) >= 2, f'{word} has fewer than two actual successors')
        two_successors[word] = dict(found[:2])
    last_pair = max(max(pairs.values()) for pairs in two_successors.values())
    require(last_pair == 573517, f'the last second successor ends at {last_pair}, not 573517')
    # Words whose preceding 3 starts before column 79 are outside the graph walk.
    initial_words = [w for w in words if w[1] == 1 or uppers[w[1] - 2] < GRAPH_START - 1]
    # The 4s.
    fours = [n for n, k in enumerate(g, 1) if k == 4]
    require(fours[0] == 3073 and uppers[3072:3074] == [4969, 4973], 'the first 4 is not at index 3073')
    distance71 = next((a, b) for a, b in zip(fours, fours[1:]) if b - a == 71)
    require(distance71 == (83418, 83489) and text[83417:83489] == EXPECTED_FILL,
            'the first consecutive 4s at distance 71 are not at 83418 and 83489 with the expected fill')
    require(min(b - a for a, b in zip(fours, fours[1:])) == 71, 'consecutive 4s closer than 71 occur')
    result = {'terms': len(g),
              'first occurrence of each return word [start, end]': dict(
                  sorted(first_word.items(), key=lambda item: item[1][1])),
              'words containing 4, first occurrence': {w: first_word[w] for w in sorted(
                  (w for w in catalogue if '4' in w), key=lambda w: first_word[w][1])},
              'two actual successors of each word that is not faithful (successor: end index)':
                  dict(sorted(two_successors.items())),
              'return words before the graph applies (word, start, end)': initial_words,
              'first 4': {'index': fours[0], 'columns': uppers[3072:3074]},
              'first consecutive 4s at distance 71': list(distance71)}
    lines = [f'first 1000000 queens: {len(g)} terms of A275888, largest 4, first 4 at index 3073 '
             f'(columns 4969 to 4973); no factor ' + ', '.join(FORBIDDEN_GAP_FACTORS),
             f'all 156 return words occur, the last ({last_word}) at indices 108002-108015',
             'every return word and successor pair in the prefix is permitted by the graph, including '
             f'the {len(initial_words)} words before the graph applies',
             f'each of the 93 words that are not faithful has two actual successors by index {last_pair}',
             'consecutive 4s at indices 83418 and 83489 attain distance 71 with the unique fill']
    return result, lines


def run() -> list[str]:
    q, uppers = upper_queen_generator(1_000_000)
    reference = bitboard_queens(200_000)
    require(q[:200_000] == reference, 'the two generators disagree in the first 200000 queens')
    runs_result, run_lines = check_column_sequences(reference[:20_000])
    g = [b - a for a, b in zip(uppers, uppers[1:])]
    gap_result, gap_lines = check_gap_prefix(g, uppers)
    RESULTS.mkdir(exist_ok=True)
    output = {'generators agree on the first queens': 200_000,
              'column runs and gaps': runs_result, 'return words and 4s': gap_result}
    (RESULTS / 'witnesses.json').write_text(json.dumps(output, indent=1) + '\n', newline='\n')
    (RESULTS / 'a275888-prefix.txt').write_text(''.join(map(str, g)) + '\n', newline='\n')
    return ['the bitboard and upper-queen generators agree on the first 200000 queens'] \
        + run_lines + gap_lines


def main() -> None:
    for line in run():
        print(line)
    print('written:', RESULTS / 'witnesses.json', 'and', RESULTS / 'a275888-prefix.txt')


if __name__ == '__main__':
    main()
