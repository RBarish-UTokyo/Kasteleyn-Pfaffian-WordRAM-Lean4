module

public import Kasteleyn.Plane.Cochain

/-!
# Kasteleyn orientations

An *orientation* of a simple graph `G` is encoded as a function `o : G.Dart → Bool` with
`o d.symm = !o d`: the edge of a dart `d` is oriented from `d.fst` to `d.snd` exactly when
`o d = true`.

For a rotation system `M` on `G`, the boundary walk of each face traverses its darts in the
direction of the face permutation (clockwise around a bounded face when the rotation is
counterclockwise). An edge on the boundary of a face `f` is *clockwise* in `f` when it is oriented
as the dart of `f` which traverses it; `cwCount o f` is the number of such darts. An orientation is
a *Kasteleyn orientation* with respect to an outer face `f₀` if every face `f ≠ f₀` has an odd
number of clockwise edges.

The definitions `Kasteleyn.IsOrientation`, `Kasteleyn.RotationSystem.cwCount` and
`Kasteleyn.RotationSystem.IsKasteleyn` are in `Kasteleyn/Spec.lean`.

## Main results

* `Kasteleyn.RotationSystem.kasteleynOrientation`: an explicit (computable) Kasteleyn
  orientation. Starting from the orientation from smaller to larger vertices, for every face
  `f ≠ f₀` with an even number of clockwise edges the edges of a path from `f` to `f₀` in a
  breadth-first spanning tree of the dual graph are reversed; this changes the parities of the
  numbers of clockwise edges exactly at `f` and `f₀`.
* `Kasteleyn.RotationSystem.isKasteleyn_kasteleynOrientation`,
  `Kasteleyn.RotationSystem.exists_isKasteleyn`: every connected rotation system has a Kasteleyn
  orientation, for any choice of the outer face.

## References

* P. W. Kasteleyn, *Dimer statistics and phase transitions*, J. Math. Phys. 4 (1963), 287–293.
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.3.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The orientation of `G` from smaller to larger vertices. -/
def orientationOfLT [LinearOrder V] (d : G.Dart) : Bool := decide (d.fst < d.snd)

lemma isOrientation_orientationOfLT [LinearOrder V] :
    IsOrientation (orientationOfLT (G := G)) := by
  intro d
  simp only [orientationOfLT, Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
  rcases lt_trichotomy d.fst d.snd with h | h | h
  · simp [h, h.not_gt]
  · exact absurd h d.fst_ne_snd
  · simp [h, h.not_gt]

/-- Reversing the edges of a set `x` of edges. -/
theorem IsOrientation.reverse {o : G.Dart → Bool} (ho : IsOrientation o) (x : G.edgeSet → Bool) :
    IsOrientation (fun d => xor (o d) (x (dartEdge d))) := by
  intro d
  simp [ho d]

namespace RotationSystem

variable (M : RotationSystem G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma cwCount_cast (o : G.Dart → Bool) (f : M.Face) :
    (M.cwCount o f : ZMod 2) = ∑ d with M.face d = f, if o d then 1 else 0 := by
  rw [cwCount, ← filter_filter, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/-- Reversing the edges of a set `x` of edges in the orientation `orientationOfLT` gives a
Kasteleyn orientation if the number of edges of `x` on each face `f ≠ f₀` has the parity of
`1 + cwCount orientationOfLT f`. -/
theorem isKasteleyn_reverse [LinearOrder V] {f₀ : M.Face} (x : G.edgeSet → ZMod 2)
    (hx : ∀ f ≠ f₀, ∑ d with M.face d = f, x (dartEdge d) = 1 + M.cwCount orientationOfLT f) :
    M.IsKasteleyn (fun d => xor (orientationOfLT d) (decide (x (dartEdge d) = 1))) f₀ := by
  refine ⟨isOrientation_orientationOfLT.reverse (fun e => decide (x e = 1)), fun f hf => ?_⟩
  rw [← ZMod.natCast_eq_one_iff_odd, cwCount_cast]
  have key : ∀ d : G.Dart, (if xor (orientationOfLT d) (decide (x (dartEdge d) = 1)) then
      (1 : ZMod 2) else 0) = (if orientationOfLT d then 1 else 0) + x (dartEdge d) := by
    intro d
    generalize x (dartEdge d) = a
    cases orientationOfLT d <;> revert a <;> decide
  rw [sum_congr rfl fun d _ => key d, sum_add_distrib, hx f hf, ← cwCount_cast,
    add_comm (1 : ZMod 2), ← add_assoc, ZMod.two_add_self, zero_add]

/-! ### An explicit construction

Let `dualBall f₀ n` be the set of faces at distance at most `n` from `f₀` in the dual graph, and
`dualDist f₀ f` the distance of `f` from `f₀`. Every face `f ≠ f₀` has a *parent dart*: the least
dart (in the lexicographic order) of `f` whose other side is closer to `f₀`. Following parent
darts from `f` leads to `f₀` along a path in the dual graph (a branch of a breadth-first spanning
tree of the dual graph); reversing the edges of this path changes the parity of the numbers of
clockwise edges exactly at `f` and at `f₀`. Reversing, starting from the orientation from smaller
to larger vertices, the paths of all faces `f ≠ f₀` with an even number of clockwise edges gives a
Kasteleyn orientation. -/

/-- The faces at distance at most `n` from `f₀` in the dual graph. -/
def dualBall (f₀ : M.Face) : ℕ → Finset M.Face
  | 0 => {f₀}
  | n + 1 => dualBall f₀ n ∪
      ({d | M.face d ∈ dualBall f₀ n} : Finset G.Dart).image fun d => M.face d.symm

lemma mem_dualBall_succ {f₀ f : M.Face} {n : ℕ} :
    f ∈ M.dualBall f₀ (n + 1) ↔
      f ∈ M.dualBall f₀ n ∨ ∃ d : G.Dart, M.face d ∈ M.dualBall f₀ n ∧ M.face d.symm = f := by
  simp [dualBall]

lemma exists_mem_dualBall (hG : G.Connected) (f₀ f : M.Face) : ∃ n, f ∈ M.dualBall f₀ n := by
  obtain ⟨d₀, hd₀⟩ := M.face_surjective f₀
  obtain ⟨d, rfl⟩ := M.face_surjective f
  have step : ∀ d : G.Dart, (∃ n, M.face d ∈ M.dualBall f₀ n) →
      ∃ n, M.face d.symm ∈ M.dualBall f₀ n := fun d ⟨n, hn⟩ =>
    ⟨n + 1, M.mem_dualBall_succ.2 (Or.inr ⟨d, hn, rfl⟩)⟩
  refine M.dart_induction hG (P := fun d => ∃ n, M.face d ∈ M.dualBall f₀ n)
    (fun d hd => ?_) step (d₀ := d₀) ⟨0, by simp [dualBall, hd₀]⟩ d
  rw [face_rot]
  exact step d hd

/-- The distance of `f` from `f₀` in the dual graph. -/
def dualDist (hG : G.Connected) (f₀ f : M.Face) : ℕ := Nat.find (M.exists_mem_dualBall hG f₀ f)

lemma mem_dualBall_dualDist (hG : G.Connected) (f₀ f : M.Face) :
    f ∈ M.dualBall f₀ (M.dualDist hG f₀ f) :=
  Nat.find_spec (M.exists_mem_dualBall hG f₀ f)

lemma dualDist_le (hG : G.Connected) {f₀ f : M.Face} {n : ℕ} (h : f ∈ M.dualBall f₀ n) :
    M.dualDist hG f₀ f ≤ n :=
  Nat.find_min' _ h

lemma dualDist_pos (hG : G.Connected) {f₀ f : M.Face} (hf : f ≠ f₀) :
    0 < M.dualDist hG f₀ f := by
  refine Nat.pos_of_ne_zero fun h => hf ?_
  have := M.mem_dualBall_dualDist hG f₀ f
  rw [h] at this
  simpa [dualBall] using this

/-- The lexicographic order on darts. -/
abbrev dartOrder [LinearOrder V] : LinearOrder G.Dart :=
  LinearOrder.lift' (fun d : G.Dart => toLex d.toProd) fun _ _ h =>
    Dart.ext _ _ (toLex.injective h)

/-- The darts of `f` whose other side is closer to `f₀`. -/
def parentDarts (hG : G.Connected) (f₀ f : M.Face) : Finset G.Dart :=
  {d | M.face d = f ∧ M.face d.symm ∈ M.dualBall f₀ (M.dualDist hG f₀ f - 1)}

lemma parentDarts_nonempty (hG : G.Connected) {f₀ f : M.Face} (hf : f ≠ f₀) :
    (M.parentDarts hG f₀ f).Nonempty := by
  have hpos := M.dualDist_pos hG hf
  have hmem := M.mem_dualBall_dualDist hG f₀ f
  rw [show M.dualDist hG f₀ f = M.dualDist hG f₀ f - 1 + 1 by omega,
    mem_dualBall_succ] at hmem
  rcases hmem with h | ⟨d, hd, rfl⟩
  · exact absurd (M.dualDist_le hG h) (by omega)
  · exact ⟨d.symm, by simp [parentDarts, hd]⟩

/-- The parent dart of a face `f ≠ f₀`: the least dart of `f` whose other side is closer
to `f₀`. -/
def parentDart [LinearOrder V] (hG : G.Connected) {f₀ f : M.Face} (hf : f ≠ f₀) : G.Dart :=
  @Finset.min' _ dartOrder (M.parentDarts hG f₀ f) (M.parentDarts_nonempty hG hf)

lemma parentDart_mem [LinearOrder V] (hG : G.Connected) {f₀ f : M.Face} (hf : f ≠ f₀) :
    M.parentDart hG hf ∈ M.parentDarts hG f₀ f :=
  @Finset.min'_mem _ dartOrder _ _

lemma face_parentDart [LinearOrder V] (hG : G.Connected) {f₀ f : M.Face} (hf : f ≠ f₀) :
    M.face (M.parentDart hG hf) = f :=
  (mem_filter.1 (M.parentDart_mem hG hf)).2.1

lemma dualDist_parentDart_lt [LinearOrder V] (hG : G.Connected) {f₀ f : M.Face}
    (hf : f ≠ f₀) : M.dualDist hG f₀ (M.face (M.parentDart hG hf).symm) < M.dualDist hG f₀ f := by
  have h1 := M.dualDist_le hG (mem_filter.1 (M.parentDart_mem hG hf)).2.2
  have h2 := M.dualDist_pos hG hf
  omega

/-- The edges of the path of parent darts from `f` to `f₀`, as a cochain. -/
def dualPath [LinearOrder V] (hG : G.Connected) (f₀ f : M.Face) : G.edgeSet → ZMod 2 :=
  if hf : f = f₀ then 0 else
    Pi.single (dartEdge (M.parentDart hG hf)) 1 +
      dualPath hG f₀ (M.face (M.parentDart hG hf).symm)
termination_by M.dualDist hG f₀ f
decreasing_by exact M.dualDist_parentDart_lt hG hf

/-- Reversing the edges of the path from `f` to `f₀` changes the parities of the numbers of
clockwise edges exactly at `f` and `f₀`. -/
theorem fibreSum_dualPath [LinearOrder V] (hG : G.Connected) (f₀ f : M.Face) :
    fibreSum M.face (M.dualPath hG f₀ f) = Pi.single f 1 + Pi.single f₀ 1 := by
  rw [dualPath]
  split_ifs with hf
  · subst hf
    funext x
    simp [ZMod.two_add_self]
  · rw [map_add, fibreSum_single, M.face_parentDart hG hf, fibreSum_dualPath hG f₀]
    funext x
    simp only [Pi.add_apply]
    rw [← add_assoc, add_assoc (Pi.single f 1 x), ZMod.two_add_self, add_zero]
termination_by M.dualDist hG f₀ f
decreasing_by exact M.dualDist_parentDart_lt hG hf

/-- The set of edges reversed by the construction: the sum of the paths to `f₀` of the faces
`f ≠ f₀` with an even number of clockwise edges for `orientationOfLT`. -/
def kasteleynFlips [LinearOrder V] (hG : G.Connected) (f₀ : M.Face) : G.edgeSet → ZMod 2 :=
  ∑ f ∈ ({f | f ≠ f₀ ∧ Even (M.cwCount orientationOfLT f)} : Finset M.Face), M.dualPath hG f₀ f

/-- **An explicit Kasteleyn orientation**: the orientation from smaller to larger vertices, with
the edges of `kasteleynFlips` reversed. -/
def kasteleynOrientation [LinearOrder V] (hG : G.Connected) (f₀ : M.Face) : G.Dart → Bool :=
  fun d => xor (orientationOfLT d) (decide (M.kasteleynFlips hG f₀ (dartEdge d) = 1))

/-- **Existence of Kasteleyn orientations.** On every connected rotation system,
`kasteleynOrientation` is a Kasteleyn orientation with respect to the outer face `f₀`. -/
theorem isKasteleyn_kasteleynOrientation [LinearOrder V] (hG : G.Connected) (f₀ : M.Face) :
    M.IsKasteleyn (M.kasteleynOrientation hG f₀) f₀ := by
  refine M.isKasteleyn_reverse _ fun f hf => ?_
  have h := congrFun (map_sum (fibreSum M.face) (fun g => M.dualPath hG f₀ g)
    ({f | f ≠ f₀ ∧ Even (M.cwCount orientationOfLT f)} : Finset M.Face)) f
  rw [← fibreSum_apply, kasteleynFlips, h, Finset.sum_apply]
  simp only [fibreSum_dualPath, Pi.add_apply, Pi.single_apply, ite_eq_right hf, add_zero]
  rw [sum_ite_eq]
  by_cases he : Even (M.cwCount orientationOfLT f)
  · rw [ite_eq_left (by simp [hf, he]), (ZMod.natCast_eq_zero_iff_even).2 he, add_zero]
  · rw [ite_eq_right (by simp [he]), (ZMod.natCast_eq_one_iff_odd).2 (Nat.not_even_iff_odd.1 he),
      ZMod.two_add_self]

/-- **Existence of Kasteleyn orientations.** Every connected rotation system has a Kasteleyn
orientation with respect to any outer face. -/
theorem exists_isKasteleyn [LinearOrder V] (hG : G.Connected) (f₀ : M.Face) :
    ∃ o : G.Dart → Bool, M.IsKasteleyn o f₀ :=
  ⟨_, M.isKasteleyn_kasteleynOrientation hG f₀⟩

end RotationSystem

end Kasteleyn
