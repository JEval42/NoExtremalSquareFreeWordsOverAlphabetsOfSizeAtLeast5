# Maximum-mean-weight cycles for square-free words

This repository contains the computer-assisted part of the paper
*No extremal square-free words over alphabets of size at least 5* by
Eng Keat Hng and Silas Rathke. In particular, `code.cpp` implements the
computation and exact verification used in Lemma 2.16.

The program

1. enumerates the realisable tuples forming the vertex set of the weighted
   digraph $G_k(S)$;
2. constructs the weighted shift graph from those tuples;
3. finds a maximum-mean directed cycle using exact policy
   iteration; and
4. verifies an exact cycle-and-potential certificate before reporting the
   result.

No floating-point calculation is used to select or certify the maximum. The
decimal printed beside each fraction is informational only.

## Requirements

- A C++17 compiler
- GNU Make (recommended, but not required)

The code has no third-party dependencies.

## Building

Build the optimized executable with:

```sh
make
```

The equivalent command is:

```sh
g++ -std=c++17 -O3 -DNDEBUG -Wall -Wextra -Wpedantic \
    -Wconversion -Wshadow code.cpp -o code
```

To use another compiler, for example Clang, run:

```sh
make CXX=clang++
```

## Quick verification

Run the small smoke test with:

```sh
make smoke
```

The relevant output is:

```text
Vertex set size: 83
Vertices: 83
Edges: 218
Maximum mean cycle: 7/8 (0.875)
Exact optimality certificate: verified
```

The reported runtime depends on the machine and is therefore not part of the
expected output.

## Reproducing the paper computations

The three instances from Lemma 2.16 can be run
separately:

```sh
make paper-result-1
make paper-result-2
make paper-result-3
```

or sequentially with:

```sh
make paper-results
```

These targets execute, respectively:

```sh
./code 10  2 13
./code 25 13 26
./code 51 26 40
```

The expected certified fractions are:

| $k$ | $S$ | Maximum mean cycle |
|---:|:---|---:|
| 10 | $\{2,\ldots,12\}$ | $10/11$ |
| 25 | $\{13,\ldots,25\}$ | $3/20$ |
| 51 | $\{26,\ldots,39\}$ | $4/45$ |

The exhaustive tuple enumeration is the dominant cost. The full instances can
take substantially longer than ten minutes and may require significant
memory, depending on the compiler and machine. Avoid running the three full
targets concurrently unless sufficient resources are available. The expected
result lines are also recorded in `results/expected-results.txt`.

## Exact certificate

Suppose the program reports a cycle of total weight $p$ and length $q$.
It also constructs an integer potential $h$ satisfying

$$
q w(u,v)-p+h(v) \le h(u)
$$

for every edge $(u,v)$. The reported cycle proves that the maximum mean is
at least $p/q$. Summing the potential inequalities around any directed cycle
proves that every cycle has mean at most \(p/q\). The program checks both the
cycle and every potential inequality using integer arithmetic before printing
`Exact optimality certificate: verified`.

Rolling hashes are used only as a fast filter during square detection. Every
hash match is followed by an exact comparison, so hash collisions cannot
change the result.

## Command-line interface

```text
./code tuple_length range_start range_end_exclusive
```

## Repository contents

- `code.cpp`: implementation and exact verifier
- `Makefile`: reproducible build and run targets
- `results/expected-results.txt`: expected certified fractions
