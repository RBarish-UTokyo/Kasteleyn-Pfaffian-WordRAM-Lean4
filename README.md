# Kasteleyn's method for plane graphs on a word RAM, in Lean 4

A Lean 4 and Mathlib formalization of Kasteleyn's method for counting the perfect matchings of plane
graphs: every rotation system of a connected graph with at least one edge has a Kasteleyn
orientation; for a plane rotation system the Pfaffian of the signed adjacency matrix is, up to sign,
the weighted sum over perfect matchings, so the number of perfect matchings is the square root of a
determinant; one program for an explicit word RAM computes a Kasteleyn orientation in linear time;
and the connected graph without edges, a single vertex with no faces in this representation, is
treated separately. All proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Author and maintainer: Robert D. Barish ([rbarish@ims.u-tokyo.ac.jp](mailto:rbarish@ims.u-tokyo.ac.jp)).

## Submission

| Challenge | Solution | Comparator configuration | Metadata | Theorems |
|---|---|---|---|---|
| `KasteleynChallenge.lean` | `KasteleynSolution.lean` | `comparator.json` | `formalization.yaml` | 5 |

The Challenge module is the statement to audit: it is self-contained, imports only Mathlib and ends
with the compared theorems proved by `sorry`. The Solution module imports the libraries of this
repository, never the Challenge. The configuration permits exactly the axioms `propext`,
`Quot.sound` and `Classical.choice`, compares no definitions separately (`definition_names` is
empty) and enables nanoda. The definitions in the Challenge are copies of the specification modules
`WordRAM/Spec.lean`, `Kasteleyn/Spec.lean` (the declarations the statements use); the comparator
checks that every constant used by the compared statements is the same kernel constant in the
Solution's environment.

## Statement

### Common definitions

**The machine (`WordRAM`).** A program is a finite list of instructions, addressed by list position.
A configuration has a program counter, natural registers and natural memory cells (`ℕ → ℕ`), real
registers and real memory cells (`ℕ → ℝ`), and an output list. The instructions are: `halt`; reading
the number of input words and the input word at a register address (`0` past the end); natural
constants, copy, `+`, truncated `-`, `*`, `/` (`0` on division by zero) and `%` (`a % 0 = a`);
natural load and store at a register address; the same for reals with real division (division by
zero is a fault); reading a word of the random tape; jumps; branches on `<` for naturals and for
reals; and appending a natural register to the output. Every instruction costs one step.
`WordRAM.RunsWithin prog P W T out` says: started on input `P` from the all-zero configuration,
`prog` executes some number `k` of instructions without fault and then stands at a `halt`
instruction, `k + 1 ≤ T` (the final `halt` is charged one step), every configuration along the run
(the last one included) has all natural registers and all natural memory cells at most `W`, and the
output at the end is `out`. Real registers are not bounded, so a program using them is not a
word-RAM program: `Instr.isReal` marks the instructions that read, write or compare reals, and
`Program.IsWord prog` says that `prog` contains none of them. The statements below require it of
every program. All inputs in the statements below have the random tape constantly `0`.

**Plane graphs as rotation systems (`Kasteleyn.RotationSystem`).** For a Mathlib simple graph `G`
(no loops, no multiple edges), a rotation system is a permutation `rot` of the darts of `G` that
keeps the initial vertex and permutes the darts leaving each vertex in a single cycle. The face
permutation sends a dart `d` to `rot (d.symm)`; the faces are its cycles, and the face of a dart is
the cycle containing it. The rotation system is *plane* (`IsPlane`) if `G` is connected and
`|V| + |F| = |E| + 2` (Euler's formula, `F` the set of faces). That such rotation systems are
exactly the combinatorial types of plane embeddings is classical and not formalized. Since faces are
cycles of darts, the one-vertex graph has no faces and is not plane in this sense: every statement
assuming `IsPlane` is about a connected graph with at least one edge.

### Kasteleyn's method (`KasteleynChallenge.lean`)

Definitions: an *orientation* is `o : G.Dart → Bool` with `o d.symm = !o d`; `cwCount o f` is the
number of darts on the boundary of the face `f` selected by `o` (the edges clockwise in `f`); `o` is
a *Kasteleyn orientation* for the outer face `f₀` if it is an orientation and every face `f ≠ f₀`
has odd `cwCount`. For a linear order on the vertices, `pf A` is the Pfaffian defined by expansion
along the least row:
`pfOn A s = Σ_{b ∈ s \ {m}} (-1)^(rank of b in s + 1) A m b · pfOn A (s \ {m, b})` with `m = min s`
and `pfOn A ∅ = 1`. `signedAdj o w` is the matrix with entry `w {x, y}` if the edge is oriented from
`x` to `y`, `-w {x, y}` if from `y` to `x`, `0` for non-adjacent `x, y`. A perfect matching of `G`
is a fixed-point-free involution `μ` of the vertices with `G.Adj x (μ x)` for all `x`. Faces are the
cycles of the face permutation on the darts, so a graph without edges has no faces here: the first
four statements are about connected graphs with at least one edge (for the Pfaffian statements this
follows from Euler's formula), and `Kasteleyn.edgeless_case` treats the connected graph without
edges. Kasteleyn's method applies to a disconnected plane graph component by component; that case is
not formalized.

* `Kasteleyn.orientation_exists`: for every finite simple graph `G` that is connected and has at
  least one edge, every rotation system `M` of `G` and every face `f₀`, there is a Kasteleyn
  orientation for `f₀`.
* `Kasteleyn.pfaffian_formula`: for a plane rotation system with a Kasteleyn orientation `o` (for
  some face `f₀`), every commutative ring `R` and all edge weights `w : Sym2 V → R`, there is
  `ε ∈ {1, -1}` with `pf (signedAdj o w) = ε · Σ_μ Π_{x < μ x} w {x, μ x}`, the sum over the perfect
  matchings of `G`.
* `Kasteleyn.matching_count`: in the same situation, with unit weights over `ℤ`, the Pfaffian is `±`
  the number of perfect matchings and the determinant of `signedAdj o 1` is its square.
* `Kasteleyn.linear_time_orientation`: there is one word program such that for every connected `G`
  with at least one edge, every rotation system with `F` faces and `S` darts, all numberings `eF` of
  the faces and `eD` of the darts and every root face `f₀`, the encoding `Orient.rotEnc M eF eD f₀`
  has `4 + F + 3S` words, and the program run on it halts within `36F + 39S + 27` steps with every
  natural word at most `4F + 5S + 8`, printing `S` words such that reading the word in the slot of
  each dart (`1` meaning forward) gives a Kasteleyn orientation for `f₀`. The encoding is
  `[F, S, r, off 0, …, off F]` followed by three words per dart slot: `r` is the index of `f₀`, the
  darts are listed face by face (sorted by face index, then dart number), `off u` is the first slot
  of face `u`, and for the dart in slot `i` the words are the face index of its reverse, the slot of
  its reverse, and an initial bit (`1` iff its number is smaller than that of its reverse).
* `Kasteleyn.edgeless_case`: a connected graph `G` without edges has exactly one vertex, no darts
  and no perfect matching, and for every orientation `o`, every commutative ring `R` and all weights
  `w`, `pf (signedAdj o w) = Σ_μ Π_{x < μ x} w {x, μ x}` (both sides are `0`) and the determinant of
  `signedAdj o 1` is the square of the number of perfect matchings (both `0`).

Kasteleyn orientations and the Pfaffian formula are Kasteleyn's (1963, 1967); see also Lovász and
Plummer, *Matching Theory*, Section 8.3. The program computes the orientation, as in Kasteleyn's
proof, along a breadth-first spanning tree of the dual graph; the program, its explicit bounds and
the edgeless case are those of this formalization.

## Libraries

Each library root module (`WordRAM.lean`, …) imports the modules of the library present here. The
libraries contain exactly the modules needed by the Solution (30 modules).

| Library | Modules | Content |
|---|---|---|
| `WordRAM` | 13 | the machine, structured programs and their compilation, the counted-operation model |
| `Kasteleyn` | 17 | Pfaffians and perfect matchings, rotation systems, faces and Kasteleyn orientations, the orientation program |

`Audit.lean` prints the axioms of the 5 compared theorems and of 35 further theorems of the
libraries.

## Checking

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib as pinned in `lakefile.toml` and
`lake-manifest.json`.

```bash
lake exe cache get && lake build
lake env lean Audit.lean    # every report names only propext, Classical.choice, Quot.sound
lake comparator --config comparator.json --paranoid
```

`lake comparator` needs `bwrap` and the toolchain's `bin` directory on `PATH`.

## License

Apache-2.0 (`LICENSE`).
