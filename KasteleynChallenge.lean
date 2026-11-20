module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Challenge: Kasteleyn orientations, Kasteleyn's theorem, and a linear-time orientation

This file is the statement a mathematical reader should audit. It states five results on
graphs drawn in the plane, given combinatorially by rotation systems. Faces are the cycles of the
face permutation on the darts, so a graph without edges has no faces here; the first four results
are about connected graphs with at least one edge, and the fifth treats the connected graph
without edges, a single vertex. Kasteleyn's method applies to a disconnected plane graph component
by component; that case is not formalized.

* `Kasteleyn.orientation_exists`: every rotation system of a connected graph with at least one
  edge has a Kasteleyn orientation (every face other than a chosen outer face has an odd number
  of clockwise edges), for any choice of the outer face;
* `Kasteleyn.pfaffian_formula`: for a plane rotation system (connected, with Euler's formula, which
  forces at least one edge) and a Kasteleyn orientation, the Pfaffian of the signed weighted
  adjacency matrix is, up to a global sign, the sum over the perfect matchings of the products of
  their edge weights;
* `Kasteleyn.matching_count`: with unit weights, the Pfaffian is plus or minus the number of
  perfect matchings, and the determinant is its square;
* `Kasteleyn.linear_time_orientation`: one fixed program for the word RAM `WordRAM` computes a
  Kasteleyn orientation of every rotation system of a connected graph with at least one edge,
  given by a standard encoding with `F` faces and `S` darts, within `36 F + 39 S + 27` steps;
* `Kasteleyn.edgeless_case`: a connected graph without edges has one vertex, no darts and no
  perfect matching, and the Pfaffian and determinant identities of the second and third results
  hold for it (both sides are `0`).

These are the results of

  P. W. Kasteleyn, *Dimer statistics and phase transitions*, J. Math. Phys. 4 (1963), 287-293;
  P. W. Kasteleyn, *Graph theory and crystal physics*, in F. Harary (ed.), *Graph Theory and
  Theoretical Physics*, Academic Press (1967), 43-110;

see also L. Lovasz and M. D. Plummer, *Matching Theory*, North-Holland (1986), Section 8.3.

The authoritative sources of every definition below are `WordRAM/Spec.lean` (the machine) and
`Kasteleyn/Spec.lean` (everything else, and the five target propositions), which the proofs import.
This file is their self-contained copy, followed by the five targets with `sorry`. The comparator
checks that every constant used by the five statements is the same kernel constant (type and value)
in the solution's environment.
-/

@[expose] public section

namespace WordRAM

/-- The input of a run: a list of words and a random tape. -/
structure Input where
  /-- The input words. -/
  data : List ℕ
  /-- The random tape. -/
  tape : ℕ → ℕ

/-- The instruction set. `r`, `a`, `b` name registers; `k` is a literal natural; `z` a literal
integer; `l` a literal instruction address. -/
inductive Instr : Type
  /-- Stop; the run has succeeded. -/
  | halt
  /-- `nreg r := n`, the number of input words. -/
  | inputSize (r : ℕ)
  /-- `nreg r := k`. -/
  | constN (r k : ℕ)
  /-- `nreg r := nreg a`. -/
  | copyN (r a : ℕ)
  /-- `nreg r := nreg a + nreg b`. -/
  | addN (r a b : ℕ)
  /-- `nreg r := nreg a - nreg b` (truncated at zero). -/
  | subN (r a b : ℕ)
  /-- `nreg r := nreg a * nreg b`. -/
  | mulN (r a b : ℕ)
  /-- `nreg r := nreg a / nreg b` (`0` if `nreg b = 0`). -/
  | divN (r a b : ℕ)
  /-- `nreg r := nreg a % nreg b` (`nreg a` if `nreg b = 0`). -/
  | modN (r a b : ℕ)
  /-- `nreg r := nmem (nreg a)`. -/
  | loadN (r a : ℕ)
  /-- `nmem (nreg a) := nreg r`. -/
  | storeN (a r : ℕ)
  /-- `rreg r := z`. -/
  | constR (r : ℕ) (z : ℤ)
  /-- `rreg r := rreg a`. -/
  | copyR (r a : ℕ)
  /-- `rreg r := rreg a + rreg b`. -/
  | addR (r a b : ℕ)
  /-- `rreg r := rreg a - rreg b`. -/
  | subR (r a b : ℕ)
  /-- `rreg r := rreg a * rreg b`. -/
  | mulR (r a b : ℕ)
  /-- `rreg r := rreg a / rreg b`; faults if `rreg b = 0`. -/
  | divR (r a b : ℕ)
  /-- `rreg r := rmem (nreg a)`. -/
  | loadR (r a : ℕ)
  /-- `rmem (nreg a) := rreg r`. -/
  | storeR (a r : ℕ)
  /-- `nreg r :=` input word number `nreg a` (`0` past the end). -/
  | readIn (r a : ℕ)
  /-- `nreg r :=` word number `nreg a` of the random tape. -/
  | rand (r a : ℕ)
  /-- `pc := l`. -/
  | jump (l : ℕ)
  /-- If `nreg a < nreg b` then `pc := l` else continue. -/
  | brLtN (a b l : ℕ)
  /-- If `rreg a < rreg b` then `pc := l` else continue. -/
  | brLtR (a b l : ℕ)
  /-- Append `nreg a` to the output. -/
  | outN (a : ℕ)

/-- A program is a finite list of instructions; instruction addresses are list positions. -/
abbrev Program : Type := List Instr

/-- A machine configuration. -/
structure Config where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers. -/
  nreg : ℕ → ℕ
  /-- Real registers. -/
  rreg : ℕ → ℝ
  /-- Natural memory. -/
  nmem : ℕ → ℕ
  /-- Real memory. -/
  rmem : ℕ → ℝ
  /-- The words output so far, in order. -/
  output : List ℕ

/-- The initial configuration: program counter `0`, all registers and memory cells zero,
nothing output. -/
def initConfig : Config :=
  { pc := 0, nreg := fun _ => 0, rreg := fun _ => 0, nmem := fun _ => 0, rmem := fun _ => 0,
    output := [] }

/-- Update one entry of a register file or memory. -/
def upd {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : ℕ → α :=
  fun j => if j = i then v else f j

/-- Execute one instruction of `prog` on input `P` from configuration `c`. Returns `none` on a
fault (program counter out of range, or real division by zero) or when the current instruction
is `halt`; otherwise the next configuration. -/
noncomputable def step (prog : Program) (P : Input) (c : Config) : Option Config :=
  match prog[c.pc]? with
  | none => none
  | some ins =>
    match ins with
    | .halt => none
    | .inputSize r => some { c with pc := c.pc + 1, nreg := upd c.nreg r P.data.length }
    | .constN r k => some { c with pc := c.pc + 1, nreg := upd c.nreg r k }
    | .copyN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a) }
    | .addN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a + c.nreg b) }
    | .subN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a - c.nreg b) }
    | .mulN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a * c.nreg b) }
    | .divN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a / c.nreg b) }
    | .modN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a % c.nreg b) }
    | .loadN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nmem (c.nreg a)) }
    | .storeN a r => some { c with pc := c.pc + 1, nmem := upd c.nmem (c.nreg a) (c.nreg r) }
    | .constR r z => some { c with pc := c.pc + 1, rreg := upd c.rreg r (z : ℝ) }
    | .copyR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a) }
    | .addR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a + c.rreg b) }
    | .subR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a - c.rreg b) }
    | .mulR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a * c.rreg b) }
    | .divR r a b =>
        if c.rreg b = 0 then none
        else some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a / c.rreg b) }
    | .loadR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rmem (c.nreg a)) }
    | .storeR a r => some { c with pc := c.pc + 1, rmem := upd c.rmem (c.nreg a) (c.rreg r) }
    | .readIn r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) }
    | .rand r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.tape (c.nreg a)) }
    | .jump l => some { c with pc := l }
    | .brLtN a b l => some { c with pc := if c.nreg a < c.nreg b then l else c.pc + 1 }
    | .brLtR a b l => some { c with pc := if c.rreg a < c.rreg b then l else c.pc + 1 }
    | .outN a => some { c with pc := c.pc + 1, output := c.output ++ [c.nreg a] }

/-- Run `k` instructions, faulting if any step faults. -/
noncomputable def run (prog : Program) (P : Input) : ℕ → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step prog P c).bind (run prog P k)

/-- The configuration is at a `halt` instruction. -/
def AtHalt (prog : Program) (c : Config) : Prop := prog[c.pc]? = some Instr.halt

/-- Every natural register and every natural memory cell of `c` is at most `W`. -/
def WordsBounded (W : ℕ) (c : Config) : Prop :=
  (∀ r, c.nreg r ≤ W) ∧ (∀ a, c.nmem a ≤ W)

/-- `prog`, started on input `P` in the initial configuration, executes exactly `k`
instructions without faulting and then sits at `halt`, every configuration along the way
(including the final one) has its natural words bounded by `W`, and the output at the end is
`out`. The run is charged `k + 1` steps: one for each executed instruction and one for the final
`halt`. -/
def RunsWithin (prog : Program) (P : Input) (W : ℕ) (steps : ℕ) (out : List ℕ) : Prop :=
  ∃ k : ℕ, k + 1 ≤ steps ∧
    (∀ i, i ≤ k → ∃ c, run prog P i initConfig = some c ∧ WordsBounded W c) ∧
    ∃ c, run prog P k initConfig = some c ∧ AtHalt prog c ∧ c.output = out

end WordRAM

end

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

/-! ### Rotation systems and faces -/

section Map

variable {V : Type*} {G : SimpleGraph V}

/-- A rotation system on a simple graph `G`: a permutation `rot` of the darts of `G` which,
for every vertex `v`, permutes the darts leaving `v` in a single cycle. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The successor of a dart in the cyclic order of the darts leaving its initial vertex. -/
  rot : Equiv.Perm G.Dart
  fst_rot : ∀ d, (rot d).fst = d.fst
  sameCycle_of_fst_eq : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

/-- The reversal of darts as a permutation. -/
def dartRev (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm _ Dart.symm_involutive

namespace RotationSystem

variable (M : RotationSystem G)

/-- The face permutation: the boundary walk of a face continues a dart `d` by the successor of
`d.symm` in the rotation at the head of `d`. -/
def faceNext : Equiv.Perm G.Dart := (dartRev G).trans M.rot

/-- The faces: the cycles of the face permutation. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.faceNext)

/-- The face of a dart: the face whose boundary walk traverses the dart. -/
def face (d : G.Dart) : M.Face := Quotient.mk _ d

section Fintype

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V]

instance : DecidableEq M.Face :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

instance : Fintype M.Face :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

/-- A rotation system is *plane* (of genus zero) if the graph is connected and Euler's formula
`V - E + F = 2` holds.

Faces are the cycles of the face permutation on the darts, so a graph without edges has no
faces here. A connected graph without edges is a single vertex; it is not plane in this sense
(`1 + 0 ≠ 0 + 2`), so statements assuming `IsPlane` leave it out. -/
structure IsPlane : Prop where
  connected : G.Connected
  euler : Fintype.card V + Fintype.card M.Face = #G.edgeFinset + 2

end Fintype

end RotationSystem

end Map

/-! ### Kasteleyn orientations -/

section Orientation

variable {V : Type*} {G : SimpleGraph V}

/-- `o` is an orientation of `G`: of the two darts of every edge, exactly one is selected. -/
def IsOrientation (o : G.Dart → Bool) : Prop := ∀ d, o d.symm = !o d

namespace RotationSystem

variable (M : RotationSystem G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The number of edges on the boundary walk of the face `f` which are clockwise in `f`, i.e.
oriented by `o` as the dart of `f` traversing them. -/
def cwCount (o : G.Dart → Bool) (f : M.Face) : ℕ := #{d | M.face d = f ∧ o d = true}

/-- A *Kasteleyn orientation* with respect to the outer face `f₀`: every face other than `f₀`
has an odd number of clockwise edges. -/
def IsKasteleyn (o : G.Dart → Bool) (f₀ : M.Face) : Prop :=
  IsOrientation o ∧ ∀ f ≠ f₀, Odd (M.cwCount o f)

end RotationSystem

end Orientation

/-! ### The Pfaffian -/

section Pfaffian

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- The rank of `x` in `s`: the number of elements of `s` strictly smaller than `x`. -/
def rankIn (s : Finset ι) (x : ι) : ℕ := #(s.filter (· < x))

/-- Auxiliary recursion for `pfOn`, with the cardinality as fuel. -/
def pfAux (A : Matrix ι ι R) : ℕ → Finset ι → R
  | 0, _ => 1
  | 1, _ => 0
  | n + 2, s =>
    if h : s.Nonempty then
      ∑ b ∈ s.erase (s.min' h),
        (-1) ^ (rankIn s b + 1) * A (s.min' h) b * pfAux A n ((s.erase (s.min' h)).erase b)
    else 0

/-- The Pfaffian of the principal submatrix of `A` with rows and columns in `s`: if `m` is the
least element of `s`, then
`pfOn A s = ∑ b ∈ s \ {m}, (-1) ^ (rankIn s b + 1) * A m b * pfOn A (s \ {m, b})`, and
`pfOn A ∅ = 1`. -/
def pfOn (A : Matrix ι ι R) (s : Finset ι) : R := pfAux A #s s

/-- The Pfaffian of a square matrix indexed by a finite linear order. -/
def pf [Fintype ι] (A : Matrix ι ι R) : R := pfOn A univ

end Pfaffian

/-! ### Perfect matchings and the signed adjacency matrix -/

section Matching

open Equiv

variable {ι : Type*}

/-- `μ` is a perfect matching of `s`: an involution of `ι` whose fixed points are exactly the
elements outside `s`. -/
def IsPerfectMatchingOn (s : Finset ι) (μ : Perm ι) : Prop :=
  (∀ x, μ (μ x) = x) ∧ ∀ x, μ x = x ↔ x ∉ s

variable [LinearOrder ι]

instance (s : Finset ι) [Fintype ι] : DecidablePred (IsPerfectMatchingOn s) := fun μ =>
  (inferInstance : Decidable ((∀ x, μ (μ x) = x) ∧ ∀ x, μ x = x ↔ x ∉ s))

/-- The finite set of perfect matchings of `s`. -/
def perfectMatchingsOn [Fintype ι] (s : Finset ι) : Finset (Perm ι) :=
  univ.filter (IsPerfectMatchingOn s)

end Matching

section SignedAdj

open Equiv

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj] {R : Type*}
  [CommRing R]

/-- The signed weighted adjacency matrix of an orientation `o` with edge weights `w`: the entry at
`(x, y)` is `w {x, y}` if the edge is oriented from `x` to `y`, `-w {x, y}` if it is oriented from
`y` to `x`, and `0` if `x` and `y` are not adjacent. -/
def signedAdj (o : G.Dart → Bool) (w : Sym2 V → R) : Matrix V V R := fun x y =>
  if h : G.Adj x y then (if o ⟨(x, y), h⟩ then w s(x, y) else -w s(x, y)) else 0

variable [Fintype V]

/-- The perfect matchings of `G`: the fixed-point-free involutions of the vertices which match
every vertex with a neighbour. -/
def graphPerfectMatchings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Perm V) :=
  (perfectMatchingsOn (univ : Finset V)).filter fun μ => ∀ x, G.Adj x (μ x)

end SignedAdj

/-! ### The machine encoding of a rotation system

The input of the orientation program for a rotation system `M` with `F` faces and `S` darts,
faces numbered by `eF`, darts numbered by `eD` and root face `f₀`, is the list of `4 + F + 3 S`
words `[F, S, r, off 0, …, off F, tg 0, rv 0, ini 0, tg 1, rv 1, ini 1, …]`: `r` is the index of
`f₀`; the darts are listed face by face, ordered by the key `(face index, eD x)`, in slots
`0, …, S - 1`; the darts of the face with index `u` occupy the slots `off u ≤ i < off (u + 1)`;
and for the dart `x` in slot `i`, `tg i` is the index of the face of `x.symm`, `rv i` the slot of
`x.symm`, and `ini i` an initial orientation bit (`1` iff `eD x < eD x.symm`). -/

namespace Orient

/-- The input of a run on the words `d`; the random tape is not used. -/
def inp (d : List ℕ) : WordRAM.Input := ⟨d, fun _ => 0⟩

/-- The list of the first `n` values of `w`. -/
def ofFun (n : ℕ) (w : ℕ → ℕ) : List ℕ := List.ofFn fun j : Fin n => w j

/-- The word `j` of the encoding of `(F, S, r, off, tg, rv, ini)`. -/
def encWord (F S r : ℕ) (ofs tgt rev bit : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = 0 then F else if j = 1 then S else if j = 2 then r else if j < 4 + F then ofs (j - 3)
  else if (j - (4 + F)) % 3 = 0 then tgt ((j - (4 + F)) / 3)
  else if (j - (4 + F)) % 3 = 1 then rev ((j - (4 + F)) / 3) else bit ((j - (4 + F)) / 3)

/-- The input `[F, S, r, off 0, …, off F, tg 0, rv 0, ini 0, …]`. -/
def enc (F S r : ℕ) (ofs tgt rev bit : ℕ → ℕ) : List ℕ :=
  ofFun (4 + F + 3 * S) (encWord F S r ofs tgt rev bit)

section rot

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (M : RotationSystem G) (eF : M.Face ≃ Fin (Fintype.card M.Face))
  (eD : G.Dart ≃ Fin (Fintype.card G.Dart))

/-- The index of the face of a dart. -/
def fi (x : G.Dart) : ℕ := eF (M.face x)

/-- The sort key of a dart: face index first. -/
def key (x : G.Dart) : ℕ := fi M eF x * Fintype.card G.Dart + eD x

/-- The slot of a dart: its rank by the key. -/
def pos (x : G.Dart) : ℕ := #{y | key M eF eD y < key M eF eD x}

/-- The first slot of the face with index `u`. -/
def ofs (u : ℕ) : ℕ := #{y : G.Dart | fi M eF y < u}

variable {M eF eD}

/-- The dart in slot `i`: a dart whose slot is `i` (there is exactly one if
`i < Fintype.card G.Dart`). -/
noncomputable def dartAt (i : ℕ) (h : i < Fintype.card G.Dart) : G.Dart :=
  @Classical.epsilon G.Dart ⟨eD.symm ⟨i, h⟩⟩ fun x => pos M eF eD x = i

variable (M eF eD)

/-- The initial orientation: from the dart with the smaller index. -/
def ini0 (x : G.Dart) : Bool := decide ((eD x : ℕ) < eD x.symm)

/-- **The input encoding a rotation system**, with root face `f₀`. -/
noncomputable def rotEnc (f₀ : M.Face) : List ℕ :=
  enc (Fintype.card M.Face) (Fintype.card G.Dart) (eF f₀) (ofs M eF)
    (fun i => if h : i < Fintype.card G.Dart then
      fi M eF (dartAt (M := M) (eF := eF) (eD := eD) i h).symm else 0)
    (fun i => if h : i < Fintype.card G.Dart then
      pos M eF eD (dartAt (M := M) (eF := eF) (eD := eD) i h).symm else 0)
    (fun i => if h : i < Fintype.card G.Dart then
      (if ini0 eD (dartAt (M := M) (eF := eF) (eD := eD) i h) then 1 else 0) else 0)

/-- The word bound used for the encoding. -/
def rotW : ℕ := 4 * Fintype.card M.Face + 5 * Fintype.card G.Dart + 8

end rot

end Orient

/-! ### The targets -/

universe u v

/-- **Existence of Kasteleyn orientations** (Kasteleyn 1963, 1967). Every rotation system of a
connected graph with at least one edge has a Kasteleyn orientation with respect to any choice of
the outer face. -/
def OrientationExists : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : RotationSystem G), G.Connected → G.edgeFinset.Nonempty →
      ∀ f₀ : M.Face, ∃ o : G.Dart → Bool, M.IsKasteleyn o f₀

/-- **Kasteleyn's theorem**, weighted form. For a plane rotation system (which has at least one
edge, see `RotationSystem.IsPlane`) with a Kasteleyn orientation `o` and edge weights `w` in a
commutative ring, the Pfaffian of the signed weighted adjacency matrix is, up to a global sign `ε =
±1`, the sum over the perfect matchings of the products of the weights of their edges. -/
def PfaffianFormula : Prop :=
  ∀ {V : Type u} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : RotationSystem G), M.IsPlane → ∀ (o : G.Dart → Bool) (f₀ : M.Face), M.IsKasteleyn o f₀ →
    ∀ (R : Type v) [CommRing R] (w : Sym2 V → R),
      ∃ ε : R, (ε = 1 ∨ ε = -1) ∧ pf (signedAdj o w) =
        ε * ∑ μ ∈ graphPerfectMatchings G, ∏ x ∈ univ with x < μ x, w s(x, μ x)

/-- **Kasteleyn's theorem**, counting form. For a plane rotation system (which has at least one
edge) with a Kasteleyn orientation `o`, the Pfaffian of the signed adjacency matrix (unit weights,
integer entries) is plus or minus the number of perfect matchings, and its determinant is the square
of that number. -/
def MatchingCount : Prop :=
  ∀ {V : Type u} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : RotationSystem G), M.IsPlane → ∀ (o : G.Dart → Bool) (f₀ : M.Face), M.IsKasteleyn o f₀ →
      (pf (signedAdj o (fun _ => (1 : ℤ))) = #(graphPerfectMatchings G) ∨
        pf (signedAdj o (fun _ => (1 : ℤ))) = -#(graphPerfectMatchings G)) ∧
      (signedAdj o (fun _ => (1 : ℤ))).det = (#(graphPerfectMatchings G) : ℤ) ^ 2

/-- **A Kasteleyn orientation in linear time.** There is one fixed program for the machine
`WordRAM` such that, for every rotation system of a connected graph with at least one edge, with
`F` faces and `S` darts, every
numbering `eF` of the faces, every numbering `eD` of the darts and every root face `f₀`, the
encoding `Orient.rotEnc M eF eD f₀` has `4 + F + 3 S` words, and the program run on it halts
within `36 F + 39 S + 27` steps, with every natural word at most `Orient.rotW M = 4 F + 5 S + 8`,
and prints `S` words; reading the word in the slot of each dart (`1` meaning forward) gives a
Kasteleyn orientation with respect to `f₀`. -/
def LinearTimeOrientation : Prop :=
  ∃ prog : WordRAM.Program,
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (M : RotationSystem G) (eF : M.Face ≃ Fin (Fintype.card M.Face))
      (eD : G.Dart ≃ Fin (Fintype.card G.Dart)), G.Connected → G.edgeFinset.Nonempty →
      ∀ f₀ : M.Face,
      (Orient.rotEnc M eF eD f₀).length = 4 + Fintype.card M.Face + 3 * Fintype.card G.Dart ∧
      ∃ out : List ℕ,
        WordRAM.RunsWithin prog (Orient.inp (Orient.rotEnc M eF eD f₀)) (Orient.rotW M)
          (36 * Fintype.card M.Face + 39 * Fintype.card G.Dart + 27) out ∧
        out.length = Fintype.card G.Dart ∧
        M.IsKasteleyn (fun x => decide (out.getD (Orient.pos M eF eD x) 0 = 1)) f₀

/-- **The graph without edges.** A connected graph without edges is a single vertex. It has no
darts, hence no faces (`RotationSystem.Face`) and no edges to orient, and it is not plane in the
sense of `RotationSystem.IsPlane`, so the statements above leave it out. Kasteleyn's identities
hold for it all the same: it has no perfect matching, and for every orientation and all weights
the Pfaffian of the signed adjacency matrix (the `1 × 1` zero matrix) equals the sum over its
perfect matchings, both being `0`, and the determinant with unit weights is the square of their
number, `0`. -/
def EdgelessCase : Prop :=
  ∀ {V : Type u} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.edgeFinset = ∅ →
      Fintype.card V = 1 ∧ IsEmpty G.Dart ∧ graphPerfectMatchings G = ∅ ∧
      ∀ (o : G.Dart → Bool) (R : Type v) [CommRing R] (w : Sym2 V → R),
        pf (signedAdj o w) = ∑ μ ∈ graphPerfectMatchings G, ∏ x ∈ univ with x < μ x, w s(x, μ x) ∧
        (signedAdj o (fun _ => (1 : ℤ))).det = (#(graphPerfectMatchings G) : ℤ) ^ 2

end Kasteleyn

end

/-! ## The targets -/

public section

namespace Kasteleyn

universe u v

/-- **Existence of Kasteleyn orientations.** -/
theorem orientation_exists : OrientationExists.{u} := by
  sorry

/-- **Kasteleyn's theorem**, weighted form. -/
theorem pfaffian_formula : PfaffianFormula.{u, v} := by
  sorry

/-- **Kasteleyn's theorem**, counting form. -/
theorem matching_count : MatchingCount.{u} := by
  sorry

/-- **A Kasteleyn orientation in linear time.** -/
theorem linear_time_orientation : LinearTimeOrientation.{u} := by
  sorry

/-- **The graph without edges.** -/
theorem edgeless_case : EdgelessCase.{u, v} := by
  sorry

end Kasteleyn

end
