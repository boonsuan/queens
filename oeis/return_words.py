"""Return words to 3 in A275888 and the faithful words (Section 6.5).

    python return_words.py

Write g for the gap sequence A275888. Cutting g immediately after each 3
gives the return words to 3. In the gap graph of a state graph (graphs.py),
the return words that begin after a 3 on the actual walk are spelled by
paths that start at the target of an edge labeled 3, avoid the label 3,
and end with one edge labeled 3.

The language. Let T be the set of targets of edges labeled 3, and consider
the edges not labeled 3 that are reachable from T. This program checks that
they form an acyclic graph, so every such path ends and the language is
finite. For each vertex v, W(v) maps each word that can be spelled from v
up to and including the next 3 to the set of vertices where it can end:
    W(v) = {3 -> targets of the 3-edges leaving v}
           together with, for each edge v --k--> t with k != 3,
           the words k w for w in W(t), with the same endpoints.
This is computed in reverse topological order. The return words permitted
by the graph are the words of W(v) for v in T. With the forty-symbol graph
there are exactly 156, and they are the 156 words of the catalogue
a275888-return-words.txt; their lengths range from 2 to 26 and exactly five
contain a 4. The twelve-symbol graph permits 247 words, so the longer
histories are needed here.

Faithful words. Every actual successor of a return word w is a word of
W(e) for some endpoint e of w. The union of these sets is Succ(w). For
exactly 63 words it has one element, so these 63 words are faithful:
every occurrence is followed by the same word. For the other 93 words,
witnesses.py finds two different actual successors, so exactly 63 words
are faithful.

Output: results/return-words.json, with every word, its successor set
Succ(w), and the faithful words with their unique successors.
"""
from __future__ import annotations

import json

import graphs
from graphs import HERE, RESULTS, require

CATALOGUE = HERE / 'a275888-return-words.txt'


def read_catalogue() -> set[str]:
    words = CATALOGUE.read_text().split('\n')
    words = [w for line in words if not line.startswith('#') for w in line.split()]
    require(len(words) == len(set(words)) == 156, 'the catalogue does not list 156 distinct words')
    return set(words)


def return_word_language(gaps: dict[int, set[tuple[int, int]]]):
    """Return (T, W) as described above: T is the set of targets of 3-edges,
    and W[v] maps each word from v to the next 3 to its set of endpoints."""
    T = {t for v in gaps for t, k in gaps[v] if k == 3}
    avoiding3 = {v: {t for t, k in gaps[v] if k != 3} for v in gaps}
    reachable, pending = set(T), list(T)
    while pending:
        for t in avoiding3[pending.pop()]:
            if t not in reachable:
                reachable.add(t)
                pending.append(t)
    order = graphs.topological_order(reachable, lambda v: avoiding3[v])
    require(order is not None, 'the edges avoiding 3 contain a reachable cycle')
    W: dict[int, dict[str, set[int]]] = {}
    for v in reversed(order):
        words: dict[str, set[int]] = {}
        for t, k in gaps[v]:
            if k == 3:
                words.setdefault('3', set()).add(t)
            else:
                for word, ends in W[t].items():
                    words.setdefault(str(k) + word, set()).update(ends)
        W[v] = words
    return T, W


def return_words(graph: graphs.StateGraph) -> dict[str, set[str]]:
    """Map each return word permitted by the graph to its successor set Succ(w)."""
    T, W = return_word_language(graphs.gap_graph(graph))
    endpoints: dict[str, set[int]] = {}
    for v in T:
        for word, ends in W[v].items():
            endpoints.setdefault(word, set()).update(ends)
    return {word: set().union(*(W[e].keys() for e in ends)) for word, ends in endpoints.items()}


def run() -> list[str]:
    twelve = return_words(graphs.twelve_symbol_graph())
    require(len(twelve) == 247, f'the twelve-symbol graph permits {len(twelve)} return words, not 247')
    successors = return_words(graphs.forty_symbol_graph())
    words = sorted(successors, key=lambda w: (len(w), w))
    require(set(words) == read_catalogue(), 'the permitted return words differ from the catalogue')
    lengths = sorted(map(len, words))
    containing4 = [w for w in words if '4' in w]
    faithful = {w: next(iter(successors[w])) for w in words if len(successors[w]) == 1}
    require((lengths[0], lengths[-1]) == (2, 26), 'return word lengths are not 2 to 26')
    require(len(containing4) == 5, 'the number of return words containing a 4 is not 5')
    require(len(faithful) == 63, f'{len(faithful)} words have one permitted successor, not 63')
    RESULTS.mkdir(exist_ok=True)
    output = {'return words': words,
              'words containing 4': containing4,
              'faithful words and their successors': faithful,
              'permitted successors': {w: sorted(successors[w], key=lambda s: (len(s), s))
                                       for w in words},
              'twelve-symbol graph': {'return words': len(twelve),
                                      'longest': max(map(len, twelve))}}
    (RESULTS / 'return-words.json').write_text(json.dumps(output, indent=2) + '\n', newline='\n')
    return [
        f'12-symbol gap graph permits {len(twelve)} return words (lengths up to {max(map(len, twelve))})',
        '40-symbol gap graph permits exactly 156 return words, equal to the catalogue',
        f'lengths {lengths[0]} to {lengths[-1]}; {len(containing4)} contain a 4: ' + ', '.join(containing4),
        f'{len(faithful)} words have a single permitted successor (faithful); '
        f'{len(words) - len(faithful)} have several',
    ]


def main() -> None:
    for line in run():
        print(line)
    print('written:', RESULTS / 'return-words.json')


if __name__ == '__main__':
    main()
