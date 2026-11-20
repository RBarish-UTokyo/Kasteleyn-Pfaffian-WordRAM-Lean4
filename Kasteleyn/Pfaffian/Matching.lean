module

public import Kasteleyn.Pfaffian.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Basic

/-!
# The Pfaffian as a signed sum over perfect matchings

A perfect matching of a finite set `s ⊆ ι` is encoded as a permutation `μ` of `ι` which is an
involution whose fixed points are exactly the elements outside `s`; each element `x ∈ s` is
matched with `μ x`. Its *crossing number* is the number of pairs of matched pairs
`{x, μ x}`, `{y, μ y}` with `x < y < μ x < μ y`, and its *weight* in a matrix `A` is the product
of the entries `A x (μ x)` over the matched pairs, each listed as `x < μ x`.

We prove the classical expansion
`pfOn A s = ∑ μ, (-1) ^ crossingNumber s μ * matchingWeight A s μ`,
the sum running over the perfect matchings of `s`. It holds for every square matrix `A`
(only the entries above the diagonal enter on either side).

## Main definitions

* `Kasteleyn.IsPerfectMatchingOn s μ`, `Kasteleyn.perfectMatchingsOn s` (in `Kasteleyn/Spec.lean`).
* `Kasteleyn.crossingNumber s μ`, `Kasteleyn.matchingWeight A s μ`.

## Main results

* `Kasteleyn.pfOn_eq_sum_perfectMatchingsOn`, `Kasteleyn.pf_eq_sum_perfectMatchings`.

## References

* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.2.
-/

@[expose] public section

namespace Kasteleyn

open Finset Equiv

variable {ι : Type*} {R : Type*} [CommRing R]

/-! ### Parity of a set with a fixed-point-free involution -/

lemma even_card_of_involution {t : Finset ι} (f : ι → ι) (hf : ∀ x ∈ t, f x ∈ t)
    (hff : ∀ x ∈ t, f (f x) = x) (hne : ∀ x ∈ t, f x ≠ x) : Even #t := by
  rw [← ZMod.natCast_eq_zero_iff_even, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_involution (fun x _ => f x) (fun _ _ => by decide) (fun x hx _ => hne x hx) hf hff

/-! ### Perfect matchings -/

namespace IsPerfectMatchingOn

variable {s : Finset ι} {μ : Perm ι} (h : IsPerfectMatchingOn s μ)
include h

lemma apply_apply (x : ι) : μ (μ x) = x := h.1 x

lemma apply_ne {x : ι} (hx : x ∈ s) : μ x ≠ x := fun e => (h.2 x).1 e hx

lemma apply_eq_self {x : ι} (hx : x ∉ s) : μ x = x := (h.2 x).2 hx

lemma apply_mem {x : ι} (hx : x ∈ s) : μ x ∈ s := by
  by_contra hc
  have := h.apply_eq_self hc
  rw [h.apply_apply] at this
  exact h.apply_ne hx this.symm

lemma apply_eq_iff {x y : ι} : μ x = y ↔ μ y = x :=
  ⟨fun e => e ▸ h.apply_apply x, fun e => e ▸ h.apply_apply y⟩

end IsPerfectMatchingOn

variable [LinearOrder ι]

@[simp] lemma mem_perfectMatchingsOn [Fintype ι] {s : Finset ι} {μ : Perm ι} :
    μ ∈ perfectMatchingsOn s ↔ IsPerfectMatchingOn s μ := by
  simp [perfectMatchingsOn]

/-- The number of crossing pairs of matched pairs: pairs `x < y` in `s` with
`x < y < μ x < μ y`. -/
def crossingNumber (s : Finset ι) (μ : Perm ι) : ℕ :=
  ∑ x ∈ s, #{y ∈ s | x < y ∧ y < μ x ∧ μ x < μ y}

/-- The weight of a matching: the product of `A x (μ x)` over the matched pairs `x < μ x`. -/
def matchingWeight (A : Matrix ι ι R) (s : Finset ι) (μ : Perm ι) : R :=
  ∏ x ∈ s with x < μ x, A x (μ x)

lemma crossingNumber_congr {s : Finset ι} {μ ν : Perm ι} (h : ∀ x ∈ s, μ x = ν x) :
    crossingNumber s μ = crossingNumber s ν := by
  refine sum_congr rfl fun x hx => ?_
  congr 1
  refine filter_congr fun y hy => ?_
  rw [h x hx, h y hy]

lemma matchingWeight_congr (A : Matrix ι ι R) {s : Finset ι} {μ ν : Perm ι}
    (h : ∀ x ∈ s, μ x = ν x) : matchingWeight A s μ = matchingWeight A s ν := by
  unfold matchingWeight
  rw [filter_congr fun x hx => by rw [h x hx]]
  refine prod_congr rfl fun x hx => ?_
  rw [h x (mem_filter.1 hx).1]

/-! ### Removing the pair of the least element -/

section Removal

variable {s : Finset ι} {μ : Perm ι} {m : ι}

/-- Removing the pair `{m, μ m}` from a perfect matching. -/
lemma isPerfectMatchingOn_swap_mul (h : IsPerfectMatchingOn s μ) (hm : m ∈ s) :
    IsPerfectMatchingOn ((s.erase m).erase (μ m)) (swap m (μ m) * μ) := by
  have key : ∀ x, (swap m (μ m) * μ) x = if x = m ∨ x = μ m then x else μ x := by
    intro x
    rw [Perm.mul_apply]
    split_ifs with hx
    · rcases hx with rfl | rfl
      · exact swap_apply_right _ _
      · rw [h.apply_apply]; exact swap_apply_left _ _
    · push Not at hx
      refine swap_apply_of_ne_of_ne (fun e => hx.2 ?_) (fun e => hx.1 ?_)
      · rw [← e, h.apply_apply]
      · exact μ.injective e
  have hother : ∀ x, ¬(x = m ∨ x = μ m) → ¬(μ x = m ∨ μ x = μ m) := by
    intro x hx hx'
    apply hx
    rcases hx' with e | e
    · right; rw [← e, h.apply_apply]
    · left; exact μ.injective e
  refine ⟨fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = m ∨ x = μ m
    · rw [key x, ite_eq_left hx, key x, ite_eq_left hx]
    · rw [key x, ite_eq_right hx, key, ite_eq_right (hother x hx), h.apply_apply]
  · rw [key x]
    by_cases hx : x = m ∨ x = μ m
    · rw [ite_eq_left hx]
      simp only [true_iff, mem_erase, not_and_or, not_not]
      rcases hx with hx | hx
      · right; left; exact hx
      · left; exact hx
    · rw [ite_eq_right hx]
      push Not at hx
      simp only [mem_erase, ne_eq, hx.1, hx.2, not_false_eq_true, true_and]
      exact h.2 x

/-- Adding a pair `{m, b}` to a perfect matching. -/
lemma isPerfectMatchingOn_swap_mul' {b : ι} {ν : Perm ι}
    (h : IsPerfectMatchingOn ((s.erase m).erase b) ν) (hm : m ∈ s) (hb : b ∈ s) (hmb : m ≠ b) :
    IsPerfectMatchingOn s (swap m b * ν) ∧ (swap m b * ν) m = b := by
  have hνm : ν m = m := h.apply_eq_self (by simp)
  have hνb : ν b = b := h.apply_eq_self (by simp)
  have hother : ∀ x, ¬(x = m ∨ x = b) → ¬(ν x = m ∨ ν x = b) := by
    intro x hx hx'
    apply hx
    rcases hx' with e | e
    · left; rw [← hνm, ← e, h.apply_apply]
    · right; rw [← hνb, ← e, h.apply_apply]
  have key : ∀ x, (swap m b * ν) x = if x = m then b else if x = b then m else ν x := by
    intro x
    rw [Perm.mul_apply]
    split_ifs with h1 h2
    · rw [h1, hνm, swap_apply_left]
    · rw [h2, hνb, swap_apply_right]
    · have := hother x (by tauto)
      push Not at this
      exact swap_apply_of_ne_of_ne this.1 this.2
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, by rw [key, ite_eq_left rfl]⟩
  · by_cases h1 : x = m
    · rw [key x, ite_eq_left h1, key, ite_eq_right hmb.symm, ite_eq_left rfl, h1]
    by_cases h2 : x = b
    · rw [key x, ite_eq_right h1, ite_eq_left h2, key, ite_eq_left rfl, h2]
    rw [key x, ite_eq_right h1, ite_eq_right h2]
    have := hother x (by tauto)
    push Not at this
    rw [key, ite_eq_right this.1, ite_eq_right this.2, h.apply_apply]
  · rw [key x]
    by_cases h1 : x = m
    · subst h1
      simp only [hm, not_true_eq_false, iff_false]
      exact Ne.symm hmb
    by_cases h2 : x = b
    · subst h2
      simp only [ite_eq_right h1, hb, not_true_eq_false, iff_false]
      exact hmb
    simp only [ite_eq_right h1, ite_eq_right h2]
    rw [h.2 x]
    simp [h1, h2]

variable (A : Matrix ι ι R)

lemma matchingWeight_eq_mul (h : IsPerfectMatchingOn s μ) (hne : s.Nonempty)
    (hm : s.min' hne = m) :
    matchingWeight A s μ = A m (μ m) * matchingWeight A ((s.erase m).erase (μ m)) μ := by
  have hms : m ∈ s := hm ▸ min'_mem s hne
  have hmlt : m < μ m := lt_of_le_of_ne (hm ▸ min'_le s _ (h.apply_mem hms)) (h.apply_ne hms).symm
  unfold matchingWeight
  rw [show s.filter (fun x => x < μ x) =
      insert m (((s.erase m).erase (μ m)).filter (fun x => x < μ x)) by
    ext x
    simp only [mem_filter, mem_insert, mem_erase]
    constructor
    · rintro ⟨hx, hlt⟩
      by_cases hxm : x = m
      · left; exact hxm
      · right
        refine ⟨⟨?_, hxm, hx⟩, hlt⟩
        rintro rfl
        rw [h.apply_apply] at hlt
        exact absurd hlt (not_lt.2 hmlt.le)
    · rintro (rfl | ⟨⟨_, _, hx⟩, hlt⟩)
      · exact ⟨hms, hmlt⟩
      · exact ⟨hx, hlt⟩]
  rw [prod_insert (by simp)]

lemma crossingNumber_eq_add (h : IsPerfectMatchingOn s μ) (hne : s.Nonempty)
    (hm : s.min' hne = m) :
    crossingNumber s μ = crossingNumber ((s.erase m).erase (μ m)) μ +
      #{y ∈ s | m < y ∧ y < μ m ∧ μ m < μ y} := by
  have hms : m ∈ s := hm ▸ min'_mem s hne
  have hmin : ∀ x ∈ s, m ≤ x := fun x hx => hm ▸ min'_le s x hx
  have hb : μ m ∈ s.erase m := mem_erase.2 ⟨h.apply_ne hms, h.apply_mem hms⟩
  unfold crossingNumber
  rw [← add_sum_erase s _ hms, ← add_sum_erase _ _ hb, h.apply_apply]
  have hzero : #{y ∈ s | μ m < y ∧ y < m ∧ m < μ y} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro y hy ⟨-, hy', -⟩
    exact absurd hy' (not_lt.2 (hmin y hy))
  rw [hzero, zero_add, add_comm]
  congr 1
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨hxb, hxm, hxs⟩ : x ≠ μ m ∧ x ≠ m ∧ x ∈ s := by simpa using hx
  congr 1
  ext y
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hy, hxy, hyμ, hμ⟩
    refine ⟨⟨?_, ?_, hy⟩, hxy, hyμ, hμ⟩
    · rintro rfl
      rw [h.apply_apply] at hμ
      exact absurd hμ (not_lt.2 (hmin _ (h.apply_mem hxs)))
    · rintro rfl
      exact absurd hxy (not_lt.2 (hmin x hxs))
  · rintro ⟨⟨-, -, hy⟩, hxy, hyμ, hμ⟩
    exact ⟨hy, hxy, hyμ, hμ⟩

lemma card_crossing_add_rankIn_even (h : IsPerfectMatchingOn s μ) (hne : s.Nonempty)
    (hm : s.min' hne = m) {b : ι} (hb : μ m = b) :
    Even (#{y ∈ s | m < y ∧ y < b ∧ b < μ y} + rankIn s b + 1) := by
  have hms : m ∈ s := hm ▸ min'_mem s hne
  have hmin : ∀ x ∈ s, m ≤ x := fun x hx => hm ▸ min'_le s x hx
  have hbm : μ b = m := by rw [← hb, h.apply_apply]
  have hmb : m < b := hb ▸ lt_of_le_of_ne (hmin _ (h.apply_mem hms)) (h.apply_ne hms).symm
  -- the elements strictly between `m` and `b` which are matched among themselves come in pairs
  have hin : Even #((s.filter fun y => m < y ∧ y < b).filter fun y => ¬ b < μ y) := by
    refine even_card_of_involution μ (fun y hy => ?_) (fun y _ => h.apply_apply y)
      (fun y hy => h.apply_ne (mem_filter.1 (mem_filter.1 hy).1).1)
    simp only [mem_filter, not_lt] at hy ⊢
    obtain ⟨⟨hys, hmy, hyb⟩, hle⟩ := hy
    have hμy : μ y ∈ s := h.apply_mem hys
    have h1 : μ y ≠ b := fun e => by
      rw [h.apply_eq_iff, hbm] at e
      exact hmy.ne e
    have h2 : μ y ≠ m := fun e => by
      rw [h.apply_eq_iff, hb] at e
      exact hyb.ne e.symm
    rw [h.apply_apply]
    exact ⟨⟨hμy, lt_of_le_of_ne (hmin _ hμy) (Ne.symm h2), lt_of_le_of_ne hle h1⟩, hyb.le⟩
  have hsplit := card_filter_add_card_filter_not (s := s.filter fun y => m < y ∧ y < b)
    (fun y => b < μ y)
  have hT : (s.filter fun y => m < y ∧ y < b).filter (fun y => b < μ y) =
      s.filter (fun y => m < y ∧ y < b ∧ b < μ y) := by
    rw [filter_filter]
    simp only [and_assoc]
  have hrank : rankIn s b = #(s.filter fun y => m < y ∧ y < b) + 1 := by
    unfold rankIn
    rw [show s.filter (· < b) = insert m (s.filter fun y => m < y ∧ y < b) by
      ext y
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hy, hyb⟩
        rcases (hmin y hy).lt_or_eq with hlt | heq
        · right; exact ⟨hy, hlt, hyb⟩
        · left; exact heq.symm
      · rintro (rfl | ⟨hy, -, hyb⟩)
        · exact ⟨hms, hmb⟩
        · exact ⟨hy, hyb⟩]
    rw [card_insert_of_notMem (by simp)]
  rw [hT] at hsplit
  obtain ⟨k, hk⟩ := hin
  exact ⟨#{y ∈ s | m < y ∧ y < b ∧ b < μ y} + k + 1, by omega⟩

end Removal

/-! ### The expansion -/

variable [Fintype ι]

/-- **The Pfaffian as a signed sum over perfect matchings**: for every square matrix `A` and
every finite set `s`, `pfOn A s` is the sum over the perfect matchings `μ` of `s` of
`(-1) ^ crossingNumber s μ * ∏ A x (μ x)`, the product running over the matched pairs
`x < μ x`. -/
theorem pfOn_eq_sum_perfectMatchingsOn (A : Matrix ι ι R) (s : Finset ι) :
    pfOn A s = ∑ μ ∈ perfectMatchingsOn s,
      (-1) ^ crossingNumber s μ * matchingWeight A s μ := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [show perfectMatchingsOn (∅ : Finset ι) = {1} by
      ext μ
      simp only [mem_perfectMatchingsOn, mem_singleton]
      constructor
      · intro h
        ext x
        exact h.apply_eq_self (notMem_empty x)
      · rintro rfl
        exact ⟨fun x => rfl, fun x => by simp⟩]
    simp [crossingNumber, matchingWeight]
  obtain ⟨m, hm⟩ : ∃ m, s.min' hne = m := ⟨_, rfl⟩
  have hms : m ∈ s := hm ▸ min'_mem s hne
  have hmin : ∀ x ∈ s, m ≤ x := fun x hx => hm ▸ min'_le s x hx
  rw [pfOn_eq_sum_min A hne, hm, ← sum_fiberwise_of_maps_to (s := perfectMatchingsOn s)
    (t := s.erase m) (g := fun μ => μ m) fun μ hμ => by
      rw [mem_perfectMatchingsOn] at hμ
      exact mem_erase.2 ⟨hμ.apply_ne hms, hμ.apply_mem hms⟩]
  refine sum_congr rfl fun b hb => ?_
  have hbs : b ∈ s := mem_of_mem_erase hb
  have hmb : m ≠ b := (ne_of_mem_erase hb).symm
  rw [ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset hms)), mul_sum]
  refine sum_nbij' (fun ν => swap m b * ν) (fun μ => swap m b * μ) ?_ ?_ ?_ ?_ ?_
  · intro ν hν
    rw [mem_perfectMatchingsOn] at hν
    obtain ⟨h1, h2⟩ := isPerfectMatchingOn_swap_mul' hν hms hbs hmb
    simpa [mem_filter, mem_perfectMatchingsOn] using ⟨h1, h2⟩
  · intro μ hμ
    obtain ⟨hμ, hμm⟩ : IsPerfectMatchingOn s μ ∧ μ m = b := by
      simpa [mem_filter, mem_perfectMatchingsOn] using hμ
    rw [mem_perfectMatchingsOn, ← hμm]
    exact isPerfectMatchingOn_swap_mul hμ hms
  · intro ν _
    exact swap_mul_self_mul m b ν
  · intro μ _
    exact swap_mul_self_mul m b μ
  · intro ν hν
    rw [mem_perfectMatchingsOn] at hν
    obtain ⟨hμ, hμm⟩ := isPerfectMatchingOn_swap_mul' hν hms hbs hmb
    set μ := swap m b * ν with hμ_def
    -- `μ` and `ν` agree on the remaining set
    have hagree : ∀ x ∈ (s.erase m).erase b, μ x = ν x := by
      intro x hx
      obtain ⟨hxb, hxm, -⟩ : x ≠ b ∧ x ≠ m ∧ x ∈ s := by simpa using hx
      rw [hμ_def, Perm.mul_apply]
      refine swap_apply_of_ne_of_ne (fun e => hxm ?_) (fun e => hxb ?_)
      · rw [← hν.apply_apply x, e, hν.apply_eq_self (by simp)]
      · rw [← hν.apply_apply x, e, hν.apply_eq_self (by simp)]
    rw [matchingWeight_eq_mul A hμ hne hm, crossingNumber_eq_add hμ hne hm, hμm,
      crossingNumber_congr hagree, matchingWeight_congr A hagree]
    obtain ⟨k, hk⟩ := card_crossing_add_rankIn_even hμ hne hm hμm
    have hsgn : (-1 : R) ^ #{y ∈ s | m < y ∧ y < b ∧ b < μ y} = (-1) ^ (rankIn s b + 1) :=
      neg_one_pow_eq_of_mod_two (by omega)
    rw [pow_add _ (crossingNumber _ ν), hsgn]
    ring

/-- **The Pfaffian as a signed sum over perfect matchings** (fixed-point-free involutions). -/
theorem pf_eq_sum_perfectMatchings (A : Matrix ι ι R) :
    pf A = ∑ μ ∈ perfectMatchingsOn (univ : Finset ι),
      (-1) ^ crossingNumber univ μ * matchingWeight A univ μ :=
  pfOn_eq_sum_perfectMatchingsOn A univ

end Kasteleyn
