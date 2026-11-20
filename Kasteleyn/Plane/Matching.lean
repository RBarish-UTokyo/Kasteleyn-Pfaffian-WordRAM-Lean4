module

public import Kasteleyn.Plane.Cycle
public import Kasteleyn.Pfaffian.Flip
public import Kasteleyn.Pfaffian.Lemmas
public import Kasteleyn.Pfaffian.Det
public import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Kasteleyn's theorem: perfect matchings of plane graphs

Let `G` be a graph on a finite linearly ordered vertex set with a plane rotation system `M`,
let `o` be a Kasteleyn orientation of `G` (with respect to some outer face), and let `w` be
weights on the edges. The *signed adjacency matrix* `signedAdj o w` has the entry `w {x, y}` at
`(x, y)` if the edge `{x, y}` is oriented from `x` to `y`, the entry `-w {x, y}` if it is
oriented from `y` to `x`, and `0` if `x` and `y` are not adjacent.

**Kasteleyn's theorem** (`Kasteleyn.pf_signedAdj_eq`): all perfect matchings of `G` contribute
with the same sign to the expansion of the Pfaffian of `signedAdj o w`, so that
`pf (signedAdj o w) = ± ∑_M ∏_{e ∈ M} w e`, the sum running over the perfect matchings of `G`.
With unit weights, `pf (signedAdj o 1) = ± #(perfect matchings)`
(`Kasteleyn.pf_signedAdj_one_eq`), and the number of perfect matchings is the square root of a
determinant (`Kasteleyn.det_signedAdj_eq`).

The proof is the classical one. Two perfect matchings `μ`, `ν` differ along disjoint alternating
cycles. Flipping `μ` along one of them, a cycle `C` of even length, multiplies its term by
`-∏ σ` around `C`, where `σ = ±1` records the orientation of each edge of `C` relative to a
traversal (`Kasteleyn.pfOn_matchingMatrix_mul_flip`). The vertices strictly inside `C` are matched
among themselves by `μ` (no edge leaves the inside of a cycle without meeting it), so there is an
even number of them, and by Kasteleyn's cycle lemma
(`Kasteleyn.RotationSystem.odd_card_fwd_add_card_inner`) an odd number of edges of `C` are oriented along the traversal: the term does not change.

## Main definitions (in `Kasteleyn/Spec.lean`)

* `Kasteleyn.signedAdj o w`: the signed weighted adjacency matrix of an orientation.
* `Kasteleyn.graphPerfectMatchings G`: the perfect matchings of `G`, as fixed-point-free
  involutions of the vertices along edges of `G`.

## References

* P. W. Kasteleyn, *The statistics of dimers on a lattice*, Physica 27 (1961), 1209–1225.
* P. W. Kasteleyn, *Dimer statistics and phase transitions*, J. Math. Phys. 4 (1963), 287–293.
* P. W. Kasteleyn, *Graph theory and crystal physics*, in *Graph Theory and Theoretical Physics*,
  Academic Press (1967), 43–110.
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.3.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph Equiv

/-! ### Alternating orbits of two involutions -/

section AltOrbit

variable {α : Type*} {μ ν : α → α}

lemma apply_iterate_of_eq_iterate (hμ : ∀ x, μ (μ x) = x) (hν : ∀ x, ν (ν x) = x) {y : α} {n : ℕ}
    (h : μ y = (ν ∘ μ)^[n] y) : ∀ i ≤ n, μ ((ν ∘ μ)^[i] y) = (ν ∘ μ)^[n - i] y := by
  intro i hi
  induction i with
  | zero => exact h
  | succ i ih =>
    have e : (ν ∘ μ)^[n - i] y = ν (μ ((ν ∘ μ)^[n - (i + 1)] y)) := by
      rw [show n - i = n - (i + 1) + 1 by omega, Function.iterate_succ_apply']
      rfl
    rw [Function.iterate_succ_apply', Function.comp_apply, ih (by omega), e, hν, hμ]

/-- In the alternating walk of two fixed-point-free involutions `μ`, `ν` starting at `y`, the
vertex `μ y` is never reached by the steps `ν ∘ μ`. -/
lemma apply_ne_iterate (hμ : ∀ x, μ (μ x) = x) (hμ' : ∀ x, μ x ≠ x) (hν : ∀ x, ν (ν x) = x)
    (hν' : ∀ x, ν x ≠ x) (y : α) (n : ℕ) : μ y ≠ (ν ∘ μ)^[n] y := by
  intro h
  have key := apply_iterate_of_eq_iterate hμ hν h
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have := key m (by omega)
    rw [show n - m = m by omega] at this
    exact hμ' _ this
  · have h1 := key (m + 1) (by omega)
    rw [show n - (m + 1) = m by omega] at h1
    have h2 : (ν ∘ μ)^[m + 1] y = μ ((ν ∘ μ)^[m] y) := by
      rw [← h1, hμ]
    have h3 : ν ((ν ∘ μ)^[m + 1] y) = (ν ∘ μ)^[m + 1] y := by
      conv_lhs => rw [Function.iterate_succ_apply', Function.comp_apply, hν]
      exact h2.symm
    exact hν' _ h3

end AltOrbit

variable {V : Type*} [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj] {R : Type*}
  [CommRing R]

/-! ### Signs and the signed adjacency matrix -/

/-- The exponent of the sign of an ordered pair: `0` if it is an edge oriented forward by `o` or a
non-edge in increasing order, `1` otherwise. -/
def signExp (o : G.Dart → Bool) (x y : V) : ℕ :=
  if h : G.Adj x y then (if o ⟨(x, y), h⟩ then 0 else 1) else (if x < y then 0 else 1)

lemma signExp_le_one (o : G.Dart → Bool) (x y : V) : signExp o x y ≤ 1 := by
  unfold signExp
  split_ifs <;> simp

lemma signExp_add {o : G.Dart → Bool} (ho : IsOrientation o) {x y : V} (hxy : x ≠ y) :
    signExp o x y + signExp o y x = 1 := by
  unfold signExp
  by_cases h : G.Adj x y
  · rw [dite_eq_left h, dite_eq_left h.symm]
    have e : (⟨(y, x), h.symm⟩ : G.Dart) = (⟨(x, y), h⟩ : G.Dart).symm := rfl
    rw [e, ho]
    cases o ⟨(x, y), h⟩ <;> rfl
  · rw [dite_eq_right h, dite_eq_right fun h' => h h'.symm]
    rcases lt_or_gt_of_ne hxy with h' | h'
    · simp [h', h'.not_gt]
    · simp [h', h'.not_gt]

lemma neg_one_pow_signExp_symm {o : G.Dart → Bool} (ho : IsOrientation o) {x y : V}
    (hxy : x ≠ y) : (-1 : R) ^ signExp o y x = -(-1) ^ signExp o x y := by
  have h := signExp_add ho hxy
  have h1 := signExp_le_one o x y
  rcases (by omega : signExp o x y = 0 ∧ signExp o y x = 1 ∨
    signExp o x y = 1 ∧ signExp o y x = 0) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> simp [h2, h3]

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : R) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

lemma signedAdj_of_adj (o : G.Dart → Bool) (w : Sym2 V → R) {x y : V} (h : G.Adj x y) :
    signedAdj o w x y = (-1) ^ signExp o x y * w s(x, y) := by
  simp only [signedAdj, signExp, dite_eq_left h]
  split_ifs <;> simp

omit [LinearOrder V] in
lemma signedAdj_of_not_adj (o : G.Dart → Bool) (w : Sym2 V → R) {x y : V} (h : ¬ G.Adj x y) :
    signedAdj o w x y = 0 := by
  simp [signedAdj, h]

/-- The signed adjacency matrix of an orientation is alternating. -/
lemma signedAdj_antisymm {o : G.Dart → Bool} (ho : IsOrientation o) (w : Sym2 V → R) (x y : V) :
    signedAdj o w y x = -signedAdj o w x y := by
  by_cases h : G.Adj x y
  · rw [signedAdj_of_adj o w h, signedAdj_of_adj o w h.symm, Sym2.eq_swap,
      neg_one_pow_signExp_symm ho (G.ne_of_adj h)]
    ring
  · rw [signedAdj_of_not_adj o w h, signedAdj_of_not_adj o w fun h' => h h'.symm, neg_zero]

omit [LinearOrder V] in
lemma signedAdj_diag (o : G.Dart → Bool) (w : Sym2 V → R) (x : V) : signedAdj o w x x = 0 :=
  signedAdj_of_not_adj o w (G.irrefl)

variable [Fintype V]

/-- The sign of a perfect matching in the expansion of the Pfaffian of a signed adjacency
matrix. -/
def matchingSign (o : G.Dart → Bool) (μ : Perm V) : R :=
  pfOn (matchingMatrix (fun x y => (-1 : R) ^ signExp o x y) univ μ) univ

omit [LinearOrder V] in
lemma isMatchingOn_univ {μ : Perm V} (h : IsPerfectMatchingOn (univ : Finset V) μ) :
    IsMatchingOn (univ : Finset V) μ :=
  fun x _ => ⟨mem_univ _, h.apply_ne (mem_univ x), h.apply_apply x⟩

lemma matchingSign_eq {o : G.Dart → Bool} {μ : Perm V}
    (hμ : IsPerfectMatchingOn (univ : Finset V) μ) :
    (matchingSign o μ : R) = (-1) ^ crossingNumber univ μ *
      ∏ x ∈ univ with x < μ x, (-1) ^ signExp o x (μ x) := by
  unfold matchingSign
  rw [pfOn_eq_sum_of_support _ univ (fun x y => μ x = y) (fun x y _ h => by
    simp [matchingMatrix, h])]
  have key : ∀ π ∈ (perfectMatchingsOn (univ : Finset V)).filter
      (fun π => ∀ x ∈ univ, x < π x → μ x = π x), π = μ := by
    intro π hπ
    simp only [mem_filter, mem_perfectMatchingsOn, mem_univ, true_implies] at hπ
    obtain ⟨hπ, h⟩ := hπ
    ext x
    rcases (hπ.apply_ne (mem_univ x)).lt_or_gt with hlt | hlt
    · have := h (π x) (by rwa [hπ.apply_apply])
      rw [hπ.apply_apply] at this
      calc π x = μ (μ (π x)) := (hμ.apply_apply _).symm
        _ = μ x := by rw [this]
    · exact (h x hlt).symm
  rw [sum_eq_single_of_mem μ (by simp [mem_filter, hμ])
    (fun π hπ hne => absurd (key π hπ) hne)]
  congr 1
  refine prod_congr rfl fun x _ => ?_
  simp [matchingMatrix]

lemma matchingSign_mul_self {o : G.Dart → Bool} (ho : IsOrientation o) {μ : Perm V}
    (hμ : IsPerfectMatchingOn (univ : Finset V) μ) :
    (matchingSign o μ : R) * matchingSign o μ = 1 :=
  pfOn_matchingMatrix_mul_self (fun _ _ hxy => neg_one_pow_signExp_symm ho hxy)
    (fun _ _ _ => neg_one_pow_mul_self _) (isMatchingOn_univ hμ)

lemma matchingSign_eq_neg_one_pow {o : G.Dart → Bool} {μ : Perm V}
    (hμ : IsPerfectMatchingOn (univ : Finset V) μ) :
    ∃ n : ℕ, (matchingSign o μ : R) = (-1) ^ n := by
  rw [matchingSign_eq hμ, prod_pow_eq_pow_sum, ← pow_add]
  exact ⟨_, rfl⟩

/-- The term of a perfect matching in the Pfaffian of the signed adjacency matrix is its sign
times the product of the weights of its edges. -/
lemma term_signedAdj {o : G.Dart → Bool} (w : Sym2 V → R) {μ : Perm V}
    (hμ : μ ∈ graphPerfectMatchings G) :
    (-1) ^ crossingNumber univ μ * matchingWeight (signedAdj o w) univ μ =
      matchingSign o μ * ∏ x ∈ univ with x < μ x, w s(x, μ x) := by
  rw [graphPerfectMatchings, mem_filter, mem_perfectMatchingsOn] at hμ
  rw [matchingSign_eq hμ.1, matchingWeight, mul_assoc, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun x _ => signedAdj_of_adj o w (hμ.2 x)

/-! ### Flipping a matching along an alternating cycle -/

variable {M : RotationSystem G}

/-- **Flipping along an alternating cycle.** If two perfect matchings `μ`, `ν` of a plane graph
with a Kasteleyn orientation differ at `x₀`, then flipping `μ` along the alternating cycle of
`μ` and `ν` through `x₀` gives a perfect matching `μ'` with the same sign, which agrees with `ν`
at more vertices. -/
lemma exists_flip (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face} (ho : M.IsKasteleyn o f₀)
    {μ ν : Perm V} (hμ : μ ∈ graphPerfectMatchings G) (hν : ν ∈ graphPerfectMatchings G)
    {x₀ : V} (hx₀ : μ x₀ ≠ ν x₀) :
    ∃ μ' ∈ graphPerfectMatchings G, #{x | μ' x ≠ ν x} < #{x | μ x ≠ ν x} ∧
      (matchingSign o μ' : R) = matchingSign o μ := by
  rw [graphPerfectMatchings, mem_filter, mem_perfectMatchingsOn] at hμ hν
  obtain ⟨hμm, hμG⟩ := hμ
  obtain ⟨hνm, hνG⟩ := hν
  have μμ : ∀ x, μ (μ x) = x := hμm.apply_apply
  have μne : ∀ x, μ x ≠ x := fun x => hμm.apply_ne (mem_univ x)
  have νν : ∀ x, ν (ν x) = x := hνm.apply_apply
  have νne : ∀ x, ν x ≠ x := fun x => hνm.apply_ne (mem_univ x)
  -- the alternating walk `a 0 = x₀, μ (a 0), a 1 = ν (μ (a 0)), …`
  set τ : V → V := ⇑ν ∘ ⇑μ with hτ
  set a : ℕ → V := fun i => τ^[i] x₀ with ha
  have hper : x₀ ∈ Function.periodicPts τ := by
    refine Function.mk_mem_periodicPts (orderOf_pos (ν * μ)) ?_
    change (⇑(ν * μ))^[orderOf (ν * μ)] x₀ = x₀
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  set k := Function.minimalPeriod τ x₀ with hk_def
  have hk : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hak : τ^[k] x₀ = x₀ := Function.iterate_minimalPeriod
  have hsucc : ∀ i, a (i + 1) = ν (μ (a i)) := fun i => Function.iterate_succ_apply' τ i x₀
  have hinj : ∀ i < k, ∀ j < k, a i = a j → i = j := fun i hi j hj h =>
    Function.iterate_injOn_Iio_minimalPeriod hi hj h
  have hmul : ∀ m i, a (k * m + i) = a i := by
    intro m i
    induction m with
    | zero => simp
    | succ m ih =>
      change τ^[k * (m + 1) + i] x₀ = τ^[i] x₀
      rw [show k * (m + 1) + i = (k * m + i) + k by ring, Function.iterate_add_apply, hak]
      exact ih
  have hmod : ∀ i, a i = a (i % k) := fun i => by
    conv_lhs => rw [← Nat.div_add_mod i k]
    exact hmul _ _
  -- the two halves of the walk are disjoint
  have hab : ∀ i j, a i ≠ μ (a j) := by
    intro i j h
    have hle : j ≤ k * j := Nat.le_mul_of_pos_left j hk
    refine apply_ne_iterate μμ μne νν νne (a j) (i + k * j - j) ?_
    rw [← h]
    change a i = τ^[i + k * j - j] (τ^[j] x₀)
    rw [← Function.iterate_add_apply, show i + k * j - j + j = k * j + i by omega]
    exact (hmul j i).symm
  have ha1 : ∀ i, a (i + 1) ≠ a i := by
    intro i h
    have h' : τ^[i] (τ x₀) = τ^[i] x₀ := by
      rw [← Function.iterate_succ_apply]
      exact h
    have h0 : ν (μ x₀) = x₀ := (Function.Injective.iterate (ν.injective.comp μ.injective) i) h'
    exact hx₀ (calc μ x₀ = ν (ν (μ x₀)) := (νν _).symm
      _ = ν x₀ := by rw [h0])
  -- the vertices of the cycle
  set A : Finset V := (range k).image a with hA
  set B : Finset V := (range k).image (fun i => μ (a i)) with hB
  set W : Finset V := A ∪ B with hW
  have memA : ∀ i, a i ∈ A := fun i =>
    mem_image.2 ⟨i % k, mem_range.2 (Nat.mod_lt _ hk), (hmod i).symm⟩
  have memB : ∀ i, μ (a i) ∈ B := fun i =>
    mem_image.2 ⟨i % k, mem_range.2 (Nat.mod_lt _ hk), by rw [← hmod i]⟩
  have hA' : ∀ y ∈ A, ∃ i, a i = y := fun y hy => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact ⟨i, rfl⟩
  have hB' : ∀ y ∈ B, ∃ i, μ (a i) = y := fun y hy => by
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    exact ⟨i, rfl⟩
  have hdisj : ∀ y ∈ A, y ∉ B := by
    intro y hy hy'
    obtain ⟨i, rfl⟩ := hA' y hy
    obtain ⟨j, hj⟩ := hB' _ hy'
    exact hab i j hj.symm
  have hνa : ∀ i, ν (a i) = μ (a (i + k - 1)) := by
    intro i
    have : a i = a (i + k - 1 + 1) := by
      rw [show i + k - 1 + 1 = k * 1 + i by omega, hmul]
    rw [this, hsucc, νν]
  have hμW : ∀ y, y ∈ W ↔ μ y ∈ W := by
    have h1 : ∀ y ∈ W, μ y ∈ W := by
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · obtain ⟨i, rfl⟩ := hA' y hy
        exact mem_union_right _ (memB i)
      · obtain ⟨i, rfl⟩ := hB' y hy
        rw [μμ]
        exact mem_union_left _ (memA i)
    exact fun y => ⟨h1 y, fun h => μμ y ▸ h1 _ h⟩
  have hνW : ∀ y ∈ W, ν y ∈ W := by
    intro y hy
    rcases mem_union.1 hy with hy | hy
    · obtain ⟨i, rfl⟩ := hA' y hy
      rw [hνa]
      exact mem_union_right _ (memB _)
    · obtain ⟨i, rfl⟩ := hB' y hy
      rw [← hsucc]
      exact mem_union_left _ (memA _)
  have hx₀W : x₀ ∈ W := mem_union_left _ (memA 0)
  -- the flipped matching
  set f : V → V := fun y => if y ∈ W then ν y else μ y with hf
  have hff : ∀ y, f (f y) = y := by
    intro y
    by_cases hy : y ∈ W
    · simp [f, hy, hνW y hy, νν]
    · have : μ y ∉ W := fun h => hy ((hμW y).2 h)
      simp [f, hy, this, μμ]
  have hfne : ∀ y, f y ≠ y := by
    intro y
    by_cases hy : y ∈ W <;> simp [f, hy, νne, μne]
  have hfadj : ∀ y, G.Adj y (f y) := by
    intro y
    by_cases hy : y ∈ W <;> simp [f, hy, hνG, hμG]
  set μ' : Perm V := Function.Involutive.toPerm f hff
  have hμ'f : (⇑μ' : V → V) = f := rfl
  have hμ'm : IsPerfectMatchingOn (univ : Finset V) μ' :=
    ⟨hff, fun x => by simp [hμ'f, hfne x]⟩
  refine ⟨μ', ?_, ?_, ?_⟩
  · rw [graphPerfectMatchings, mem_filter, mem_perfectMatchingsOn]
    exact ⟨hμ'm, hfadj⟩
  · -- fewer disagreements with `ν`
    refine card_lt_card ((ssubset_iff_of_subset fun x hx => ?_).2 ⟨x₀, ?_, ?_⟩)
    · simp only [mem_filter, mem_univ, true_and, hμ'f, f] at hx ⊢
      by_cases hxW : x ∈ W
      · simp [hxW] at hx
      · simpa [hxW] using hx
    · simp [hx₀]
    · simp [hμ'f, f, hx₀W]
  -- the sign
  set σ : V → V → R := fun x y => (-1) ^ signExp o x y with hσ_def
  have hσ : ∀ x y, x ≠ y → σ y x = -σ x y := fun x y hxy => neg_one_pow_signExp_symm ho.1 hxy
  have hσ1 : ∀ x y, x ≠ y → σ x y * σ x y = 1 := fun x y _ => neg_one_pow_mul_self _
  set g : ℕ → V × V := fun i => (a i, μ (a i)) with hg
  have hchain : ∀ n j, a (j + n) = x₀ → AltChain f x₀ ((List.range' j n).map g) := by
    intro n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      rw [List.range'_succ, List.map_cons, altChain_cons]
      refine ⟨?_, ih (j + 1) (by rw [← hj]; congr 1; omega)⟩
      have h1 : f (g j).2 = a (j + 1) := by
        simp only [g, f, ite_eq_left ((hμW _).1 (mem_union_left _ (memA j))), hsucc]
      rw [h1]
      cases n with
      | zero => simpa using hj
      | succ n => rw [List.range'_succ, List.map_cons, nextFst_cons]
  have hprod : ∀ n j, a (j + n) = x₀ → altProd σ x₀ ((List.range' j n).map g) =
      ∏ i ∈ range n, σ (a (j + i)) (μ (a (j + i))) * σ (μ (a (j + i))) (a (j + i + 1)) := by
    intro n
    induction n with
    | zero => intro j _; simp
    | succ n ih =>
      intro j hj
      rw [List.range'_succ, List.map_cons, altProd_cons, ih (j + 1) (by rw [← hj]; congr 1; omega),
        prod_range_succ']
      have h1 : nextFst x₀ ((List.range' (j + 1) n).map g) = a (j + 1) := by
        cases n with
        | zero => simpa using hj.symm
        | succ n => rw [List.range'_succ, List.map_cons, nextFst_cons]
      rw [h1]
      simp only [g, add_zero]
      rw [mul_comm]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      rw [show j + 1 + i = j + (i + 1) by omega]
  have hk0 : a (0 + k) = x₀ := by rw [zero_add]; exact hak
  -- the list of pairs of the cycle
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hP : (List.range' 0 k).map g = (x₀, μ x₀) :: (List.range' 1 k').map g := by
    rw [hk', List.range'_succ, List.map_cons]
    rfl
  have hmemP : ∀ x, x ∈ pairVerts ((List.range' 0 k).map g) ↔ x ∈ W := by
    intro x
    rw [pairVerts_map, List.mem_flatMap]
    constructor
    · rintro ⟨i, -, hi⟩
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact mem_union_left _ (memA i)
      · exact mem_union_right _ (memB i)
    · intro hx
      rcases mem_union.1 hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        exact ⟨i, List.mem_range'_1.2 ⟨by omega, by simpa using hi⟩, by simp [g]⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        exact ⟨i, List.mem_range'_1.2 ⟨by omega, by simpa using hi⟩, by simp [g]⟩
  have hnd : (pairVerts ((List.range' 0 k).map g)).Nodup := by
    rw [pairVerts_map, List.nodup_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · simp only [g, List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      exact hab i i
    · refine (List.pairwise_lt_range' (s := 0) (n := k)).imp_of_mem fun {i j} hi hj hij => ?_
      rw [List.mem_range'_1] at hi hj
      have hne : a i ≠ a j := fun h => (hinj i (by omega) j (by omega) h ▸ hij).false
      show List.Disjoint _ _
      rw [List.disjoint_left]
      intro x hx hx'
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | h
      · exact hne h
      · exact hab i j h
      · exact hab j i h.symm
      · exact hne (μ.injective h)
  have hflip := pfOn_matchingMatrix_mul_flip (σ := σ) (s := univ) (m := μ) (m' := f) hσ hσ1
    x₀ (μ x₀) ((List.range' 1 k').map g) (isMatchingOn_univ hμm) (isMatchingOn_univ hμ'm)
    (hP ▸ hnd) (fun _ _ => mem_univ _)
    (by
      rw [← hP]
      intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
      rfl)
    (hP ▸ hchain k 0 hk0)
    (by
      intro x _ hx
      rw [← hP, hmemP] at hx
      simp [f, hx])
  rw [← hP, hprod k 0 hk0] at hflip
  -- the cycle as a cycle of the graph
  set C : GraphCycle G :=
    { verts := W
      next := fun y => if y ∈ A then μ y else ν y
      next_mem := by
        intro v hv
        by_cases hvA : v ∈ A
        · simp only [hvA, ite_true]
          exact (hμW v).1 hv
        · simp only [hvA, ite_false]
          exact hνW v hv
      adj_next := by
        intro v _
        by_cases hvA : v ∈ A <;> simp [hvA, hμG, hνG]
      next_injOn := by
        intro u hu v hv h
        have hu' := mem_union.1 hu
        have hv' := mem_union.1 hv
        by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A <;> simp only [huA, hvA, ite_true,
          ite_false] at h
        · exact μ.injective h
        · have h1 : μ u ∈ B := by
            obtain ⟨i, rfl⟩ := hA' u huA
            exact memB i
          have h2 : ν v ∈ A := by
            obtain ⟨i, rfl⟩ := hB' v (hv'.resolve_left hvA)
            rw [← hsucc]
            exact memA _
          exact absurd (h ▸ h2) (fun h3 => hdisj _ h3 h1)
        · have h1 : μ v ∈ B := by
            obtain ⟨i, rfl⟩ := hA' v hvA
            exact memB i
          have h2 : ν u ∈ A := by
            obtain ⟨i, rfl⟩ := hB' u (hu'.resolve_left huA)
            rw [← hsucc]
            exact memA _
          exact absurd (h ▸ h2) (fun h3 => hdisj _ h3 h1)
        · exact ν.injective h
      next_next_ne := by
        intro v hv
        by_cases hvA : v ∈ A
        · obtain ⟨i, rfl⟩ := hA' v hvA
          have : μ (a i) ∉ A := fun h => hdisj _ h (memB i)
          simp only [hvA, ite_true, this, ite_false]
          rw [← hsucc]
          exact ha1 i
        · obtain ⟨i, rfl⟩ := hB' v ((mem_union.1 hv).resolve_left hvA)
          simp only [hvA, ite_false]
          rw [← hsucc, ite_eq_left (memA _)]
          exact fun h => ha1 i (μ.injective h)
      reach := by
        have hnext : ∀ m i, (fun y => if y ∈ A then μ y else ν y)^[2 * m] (a i) = a (i + m) := by
          intro m
          induction m with
          | zero => intro i; rfl
          | succ m ih =>
            intro i
            rw [show 2 * (m + 1) = 2 + 2 * m by ring, Function.iterate_add_apply, ih,
              Function.iterate_succ_apply', Function.iterate_one]
            have : μ (a (i + m)) ∉ A := fun h => hdisj _ h (memB _)
            simp only [memA, ite_true, this, ite_false]
            rw [← hsucc]
            exact congrArg a (by omega)
        have hto : ∀ y ∈ W, ∃ n, (fun y => if y ∈ A then μ y else ν y)^[n] y = x₀ := by
          intro y hy
          rcases mem_union.1 hy with hy | hy
          · obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
            refine ⟨2 * (k - i), ?_⟩
            rw [hnext, show i + (k - i) = k by have := mem_range.1 hi; omega]
            exact hak
          · obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
            refine ⟨2 * (k - (i + 1)) + 1, ?_⟩
            have : μ (a i) ∉ A := fun h => hdisj _ h (memB _)
            rw [Function.iterate_add_apply, Function.iterate_one]
            simp only [this, ite_false]
            rw [← hsucc, hnext, show i + 1 + (k - (i + 1)) = k by have := mem_range.1 hi; omega]
            exact hak
        have hfrom : ∀ y ∈ W, ∃ n, (fun y => if y ∈ A then μ y else ν y)^[n] x₀ = y := by
          intro y hy
          rcases mem_union.1 hy with hy | hy
          · obtain ⟨i, -, rfl⟩ := mem_image.1 hy
            exact ⟨2 * i, by rw [show x₀ = a 0 from rfl, hnext, zero_add]⟩
          · obtain ⟨i, -, rfl⟩ := mem_image.1 hy
            refine ⟨1 + 2 * i, ?_⟩
            rw [Function.iterate_add_apply, show x₀ = a 0 from rfl, hnext, zero_add,
              Function.iterate_one]
            simp [memA]
        intro u hu v hv
        obtain ⟨n₁, hn₁⟩ := hto u hu
        obtain ⟨n₂, hn₂⟩ := hfrom v hv
        exact ⟨n₂ + n₁, by rw [Function.iterate_add_apply, hn₁, hn₂]⟩
      nonempty := ⟨x₀, hx₀W⟩ } with hC
  -- the number of backward edges of the cycle
  have hback : #({d | C.IsFwd d ∧ o d = false} : Finset G.Dart) =
      ∑ i ∈ range k, (signExp o (a i) (μ (a i)) + signExp o (μ (a i)) (a (i + 1))) := by
    have e1 : #({d | C.IsFwd d ∧ o d = false} : Finset G.Dart) =
        ∑ d ∈ ({d | C.IsFwd d} : Finset G.Dart), signExp o d.fst d.snd := by
      rw [← filter_filter, card_filter]
      refine sum_congr rfl fun d _ => ?_
      simp only [signExp, dite_eq_left d.adj]
      cases o d <;> rfl
    have e2 : ∑ d ∈ ({d | C.IsFwd d} : Finset G.Dart), signExp o d.fst d.snd =
        ∑ u ∈ W, signExp o u (C.next u) := by
      refine sum_bij (fun d _ => d.fst) (fun d hd => (mem_filter.1 hd).2.1)
        (fun d hd d' hd' h => ?_) (fun u hu => ⟨C.outDart u hu, by simp [C.isFwd_outDart], rfl⟩)
        (fun d hd => by rw [(mem_filter.1 hd).2.2])
      rw [C.eq_outDart (mem_filter.1 hd).2, C.eq_outDart (mem_filter.1 hd').2]
      exact Dart.ext _ _ (Prod.ext h (by simp [h]))
    rw [e1, e2, sum_union (disjoint_left.2 hdisj), sum_add_distrib]
    congr 1
    · rw [sum_image fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) h]
      exact sum_congr rfl fun i _ => by simp [C, memA]
    · rw [sum_image fun i hi j hj h => hinj i (mem_range.1 hi) j (mem_range.1 hj) (μ.injective h)]
      refine sum_congr rfl fun i _ => ?_
      have : μ (a i) ∉ A := fun h => hdisj _ h (memB _)
      simp [C, this, hsucc]
  -- parity: the cycle has an odd number of backward edges
  obtain ⟨I, hI, hf₀I⟩ := RotationSystem.exists_inside hM C f₀
  have hW2 : Even #W := even_card_of_involution μ (fun x hx => (hμW x).1 hx)
    (fun x _ => μμ x) (fun x _ => μne x)
  have hin2 : Even #(M.regionVerts I \ W) := by
    refine even_card_of_involution μ (fun x hx => ?_) (fun x _ => μμ x) (fun x _ => μne x)
    obtain ⟨hxI, hxW⟩ := mem_sdiff.1 hx
    have h := hI.snd_mem_regionVerts (d := ⟨(x, μ x), hμG x⟩) hxW hxI
    exact mem_sdiff.2 ⟨h.1, fun h' => hxW ((hμW x).2 h')⟩
  have hCv : C.verts = W := rfl
  have hodd := RotationSystem.odd_card_fwd_add_card_inner hM ho C hW2 hI hf₀I
  rw [hCv] at hodd
  have hsplit := card_filter_add_card_filter_not (s := ({d | C.IsFwd d} : Finset G.Dart))
    (p := fun d => o d = true)
  simp only [filter_filter, Bool.not_eq_true] at hsplit
  rw [C.card_isFwd, hCv] at hsplit
  have hbodd : Odd #({d | C.IsFwd d ∧ o d = false} : Finset G.Dart) := by
    obtain ⟨m₁, hm₁⟩ := hW2
    obtain ⟨m₂, hm₂⟩ := hin2
    rw [Nat.odd_iff] at hodd ⊢
    change #W = m₁ + m₁ at hm₁
    omega
  have hcyc : altProd σ x₀ ((List.range' 0 k).map g) = -1 := by
    rw [hprod k 0 hk0]
    simp only [zero_add, σ, ← pow_add, prod_pow_eq_pow_sum, ← hback]
    exact hbodd.neg_one_pow
  rw [hprod k 0 hk0] at hcyc
  rw [hcyc, neg_neg] at hflip
  -- conclusion
  have h1 : (matchingSign o μ' : R) * matchingSign o μ' = 1 := matchingSign_mul_self ho.1 hμ'm
  have h2 : (matchingSign o μ : R) * matchingSign o μ' = 1 := hflip
  calc (matchingSign o μ' : R) = matchingSign o μ' * (matchingSign o μ * matchingSign o μ') := by
        rw [h2, mul_one]
    _ = matchingSign o μ * (matchingSign o μ' * matchingSign o μ') := by ring
    _ = matchingSign o μ := by rw [h1, mul_one]

/-! ### Kasteleyn's theorem -/

/-- **All perfect matchings of a plane graph have the same sign** in the Pfaffian of a signed
adjacency matrix of a Kasteleyn orientation. -/
theorem matchingSign_eq_of_mem (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) {μ ν : Perm V} (hμ : μ ∈ graphPerfectMatchings G)
    (hν : ν ∈ graphPerfectMatchings G) : (matchingSign o μ : R) = matchingSign o ν := by
  suffices h : ∀ n, ∀ μ ∈ graphPerfectMatchings G, #{x | μ x ≠ ν x} = n →
      (matchingSign o μ : R) = matchingSign o ν from h _ μ hμ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro μ hμ hn
  by_cases heq : μ = ν
  · rw [heq]
  obtain ⟨x₀, hx₀⟩ : ∃ x, μ x ≠ ν x := by
    by_contra h
    push Not at h
    exact heq (Equiv.ext h)
  obtain ⟨μ', hμ', hlt, hsign⟩ := exists_flip (R := R) hM ho hμ hν hx₀
  rw [← hsign]
  exact ih _ (hn ▸ hlt) μ' hμ' rfl

/-- **Kasteleyn's theorem** (weighted form). Let `G` be a plane graph with a Kasteleyn
orientation `o` and edge weights `w`. Then the Pfaffian of the signed adjacency matrix is, up to
a global sign, the sum over the perfect matchings of `G` of the products of the weights of their
edges. -/
theorem pf_signedAdj_eq (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) (w : Sym2 V → R) :
    ∃ ε : R, (ε = 1 ∨ ε = -1) ∧ pf (signedAdj o w) =
      ε * ∑ μ ∈ graphPerfectMatchings G, ∏ x ∈ univ with x < μ x, w s(x, μ x) := by
  have h := pf_eq_sum_of_adj G (signedAdj o w) fun x y h => signedAdj_of_not_adj o w h
  change pf (signedAdj o w) = ∑ μ ∈ graphPerfectMatchings G, _ at h
  rcases (graphPerfectMatchings G).eq_empty_or_nonempty with he | ⟨ν, hν⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [h, he, sum_empty, sum_empty, mul_zero]
  have hνm : IsPerfectMatchingOn (univ : Finset V) ν :=
    mem_perfectMatchingsOn.1 (mem_filter.1 hν).1
  obtain ⟨n, hn⟩ := matchingSign_eq_neg_one_pow (R := R) (o := o) hνm
  refine ⟨matchingSign o ν, hn ▸ neg_one_pow_eq_or R n, ?_⟩
  rw [h, mul_sum]
  refine sum_congr rfl fun μ hμ => ?_
  rw [term_signedAdj w hμ, matchingSign_eq_of_mem hM ho hμ hν]

/-- **Kasteleyn's theorem.** For a Kasteleyn orientation of a plane graph, the Pfaffian of the
signed adjacency matrix is, up to sign, the number of perfect matchings of the graph. -/
theorem pf_signedAdj_one_eq (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) :
    ∃ ε : R, (ε = 1 ∨ ε = -1) ∧
      pf (signedAdj o (fun _ => (1 : R))) = ε * #(graphPerfectMatchings G) := by
  obtain ⟨ε, hε, h⟩ := pf_signedAdj_eq (R := R) hM ho fun _ => 1
  refine ⟨ε, hε, ?_⟩
  rw [h]
  simp

/-- **Counting perfect matchings by a determinant.** For a Kasteleyn orientation of a plane
graph, the determinant of the signed adjacency matrix is the square of the number of perfect
matchings. -/
theorem det_signedAdj_eq (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) :
    (signedAdj o (fun _ => (1 : R))).det = (#(graphPerfectMatchings G) : R) ^ 2 := by
  obtain ⟨ε, hε, h⟩ := pf_signedAdj_one_eq (R := R) hM ho
  rw [← pf_sq (signedAdj_diag o _) (signedAdj_antisymm ho.1 _), h, mul_pow]
  rcases hε with rfl | rfl <;> simp

/-- **The number of perfect matchings of a plane graph**: a Kasteleyn orientation exists, and
for it the Pfaffian of the signed adjacency matrix is plus or minus the number of perfect
matchings; its determinant is the square of that number. -/
theorem exists_det_signedAdj_eq (hM : M.IsPlane) (f₀ : M.Face) :
    ∃ o : G.Dart → Bool, M.IsKasteleyn o f₀ ∧
      ((pf (signedAdj o (fun _ => (1 : R))) = #(graphPerfectMatchings G) ∨
        pf (signedAdj o (fun _ => (1 : R))) = -#(graphPerfectMatchings G)) ∧
      (signedAdj o (fun _ => (1 : R))).det = (#(graphPerfectMatchings G) : R) ^ 2) := by
  obtain ⟨o, ho⟩ := M.exists_isKasteleyn hM.connected f₀
  refine ⟨o, ho, ?_, det_signedAdj_eq hM ho⟩
  obtain ⟨ε, hε, h⟩ := pf_signedAdj_one_eq (R := R) hM ho
  rcases hε with rfl | rfl
  · left; rw [h, one_mul]
  · right; rw [h, neg_one_mul]

end Kasteleyn
