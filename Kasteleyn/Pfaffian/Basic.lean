module

public import Kasteleyn.Spec
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Ring

/-!
# The Pfaffian

For a square matrix `A` indexed by a linearly ordered type `ι` and a finite set `s : Finset ι`,
`Kasteleyn.pfOn A s` is the Pfaffian of the principal submatrix of `A` on the rows and columns
in `s` (listed in increasing order). It is defined by the classical expansion along the first
row: if `m` is the least element of `s`, then
`pfOn A s = ∑ b ∈ s \ {m}, (-1) ^ (rankIn s b + 1) * A m b * pfOn A (s \ {m, b})`,
where `rankIn s b` is the number of elements of `s` below `b`, and `pfOn A ∅ = 1`.
In particular the Pfaffian of a set of odd cardinality vanishes.

For `[Fintype ι]`, `Kasteleyn.pf A = pfOn A univ` is the Pfaffian of `A` itself.

## Main results

* `Kasteleyn.pfOn_eq_sum_min`: the expansion along the row of the least element.
* `Kasteleyn.pfOn_expand`: for a skew-symmetric `A`, the expansion along an arbitrary row `a`,
  with the sign `pairSign s a b = (-1) ^ (rankIn s a + rankIn s b + [a < b])`.
* `Kasteleyn.pfOn_eq_zero_of_odd`: the Pfaffian of an odd set vanishes.

## References

* A. Cayley, *Sur les déterminants gauches*, J. reine angew. Math. 38 (1849).
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.2.
-/

@[expose] public section

namespace Kasteleyn

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-! ### Ranks and signs -/

/-- The indicator `[a < b]` as a natural number. -/
def ltInd (a b : ι) : ℕ := if a < b then 1 else 0

lemma ltInd_of_lt {a b : ι} (h : a < b) : ltInd a b = 1 := by simp [ltInd, h]

lemma ltInd_of_le {a b : ι} (h : b ≤ a) : ltInd a b = 0 := by simp [ltInd, not_lt.2 h]

lemma ltInd_add_ltInd {a b : ι} (h : a ≠ b) : ltInd a b + ltInd b a = 1 := by
  rcases h.lt_or_gt with h | h
  · rw [ltInd_of_lt h, ltInd_of_le h.le]
  · rw [ltInd_of_lt h, ltInd_of_le h.le]

lemma rankIn_erase {s : Finset ι} {a : ι} (ha : a ∈ s) (x : ι) :
    rankIn s x = rankIn (s.erase a) x + ltInd a x := by
  unfold rankIn ltInd
  simp only [filter_erase]
  split_ifs with h
  · rw [card_erase_of_mem (mem_filter.2 ⟨ha, h⟩)]
    have : 0 < #(s.filter (· < x)) := card_pos.2 ⟨a, mem_filter.2 ⟨ha, h⟩⟩
    omega
  · rw [erase_eq_of_notMem (s := s.filter (· < x)) (fun h' => h (mem_filter.1 h').2)]
    rfl

lemma rankIn_min' {s : Finset ι} (h : s.Nonempty) : rankIn s (s.min' h) = 0 := by
  unfold rankIn
  rw [card_eq_zero, filter_eq_empty_iff]
  exact fun x hx => not_lt.2 (min'_le s x hx)

/-- The sign attached to the pair `a, b` of elements of `s` in the expansion of the Pfaffian
along the row `a`: `(-1) ^ (rankIn s a + rankIn s b + [a < b])`. -/
def pairSign (s : Finset ι) (a b : ι) : R := (-1) ^ (rankIn s a + rankIn s b + ltInd a b)

lemma neg_one_pow_eq_of_mod_two {m n : ℕ} (h : m % 2 = n % 2) : (-1 : R) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-! ### The definition

`rankIn`, `pfAux`, `pfOn` and `pf` are defined in `Kasteleyn/Spec.lean`. -/

variable (A : Matrix ι ι R)

@[simp] lemma pfOn_empty : pfOn A ∅ = 1 := rfl

lemma pf_def [Fintype ι] : pf A = pfOn A univ := rfl

/-- Expansion of the Pfaffian along the row of the least element. -/
theorem pfOn_eq_sum_min {s : Finset ι} (h : s.Nonempty) :
    pfOn A s = ∑ b ∈ s.erase (s.min' h),
      (-1) ^ (rankIn s b + 1) * A (s.min' h) b * pfOn A ((s.erase (s.min' h)).erase b) := by
  have key : ∀ b ∈ s.erase (s.min' h), #((s.erase (s.min' h)).erase b) = #s - 2 := by
    intro b hb
    rw [card_erase_of_mem hb, card_erase_of_mem (min'_mem s h)]
    omega
  unfold pfOn
  rcases hs : #s with _ | _ | n
  · exact absurd hs (card_ne_zero.2 h)
  · obtain ⟨x, rfl⟩ := card_eq_one.1 hs
    simp [pfAux]
  · simp only [pfAux, h, dite_true]
    refine sum_congr rfl fun b hb => ?_
    rw [key b hb, hs]
    rfl

theorem pfOn_singleton (a : ι) : pfOn A {a} = 0 := by
  rw [pfOn_eq_sum_min A (singleton_nonempty a)]
  simp

theorem pfOn_pair {a b : ι} (h : a < b) : pfOn A {a, b} = A a b := by
  have hne : ({a, b} : Finset ι).Nonempty := insert_nonempty _ _
  have hmin : ({a, b} : Finset ι).min' hne = a :=
    le_antisymm (min'_le _ _ (mem_insert_self _ _))
      (le_min' _ _ _ (by simp [h.le]))
  rw [pfOn_eq_sum_min A hne, hmin, erase_insert (by simp [h.ne])]
  have hr : rankIn {a, b} b = 1 := by
    unfold rankIn
    rw [show ({a, b} : Finset ι).filter (· < b) = {a} by
      ext x
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩]
    rfl
  simp [hr]

theorem pfAux_eq_zero_of_odd (n : ℕ) (hn : Odd n) (s : Finset ι) : pfAux A n s = 0 := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  match n, hn, ih with
  | 0, hn, _ => exact absurd hn (by decide)
  | 1, _, _ => rfl
  | n + 2, hn, ih =>
    rw [pfAux]
    split_ifs
    · refine sum_eq_zero fun b _ => ?_
      rw [ih n (by omega) (by simpa [Nat.odd_add] using hn), mul_zero]
    · rfl

theorem pfOn_eq_zero_of_odd {s : Finset ι} (hs : Odd #s) : pfOn A s = 0 :=
  pfAux_eq_zero_of_odd A _ hs s

/-! ### Expansion along an arbitrary row -/

lemma min'_eq_of_mem_subset {s t : Finset ι} (hs : s.Nonempty) (ht : t.Nonempty) (hts : t ⊆ s)
    (hm : s.min' hs ∈ t) : t.min' ht = s.min' hs :=
  le_antisymm (min'_le t _ hm) (le_min' _ _ _ fun x hx => min'_le s x (hts hx))

/-- Expansion of the Pfaffian of a skew-symmetric matrix along an arbitrary row `a ∈ s`. -/
theorem pfOn_expand {A : Matrix ι ι R} (hA : ∀ i j, A j i = -A i j) {s : Finset ι} {a : ι}
    (ha : a ∈ s) :
    pfOn A s = ∑ b ∈ s.erase a, pairSign s a b * A a b * pfOn A ((s.erase a).erase b) := by
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
  have hne : s.Nonempty := ⟨a, ha⟩
  have hmem : s.min' hne ∈ s := min'_mem s hne
  rw [pfOn_eq_sum_min A hne]
  by_cases ham : a = s.min' hne
  · rw [← ham]
    refine sum_congr rfl fun b hb => ?_
    have hab : a < b := ham ▸ min'_lt_of_mem_erase_min' s hne (ham ▸ hb)
    rw [pairSign, ham, rankIn_min', ← ham, ltInd_of_lt hab, zero_add]
  -- the general case
  set m := s.min' hne with hm_def
  have hma : m < a := lt_of_le_of_ne (min'_le s a ha) (Ne.symm ham)
  have ha' : a ∈ s.erase m := mem_erase.2 ⟨ham, ha⟩
  have hm' : m ∈ s.erase a := mem_erase.2 ⟨hma.ne, hmem⟩
  rw [← add_sum_erase _ _ ha', ← add_sum_erase _ _ hm']
  congr 1
  · rw [erase_right_comm, hA m a, pairSign, hm_def, rankIn_min', ← hm_def,
      ltInd_of_le hma.le]
    ring
  set U := (s.erase m).erase a with hU
  have hU' : (s.erase a).erase m = U := erase_right_comm
  rw [hU']
  -- expand the left-hand side along the row `a`, using the induction hypothesis
  have L : ∀ b ∈ U, pfOn A ((s.erase m).erase b) = ∑ c ∈ U.erase b,
      pairSign ((s.erase m).erase b) a c * A a c *
        pfOn A ((((s.erase m).erase b).erase a).erase c) := by
    intro b hb
    have hba : b ≠ a := (mem_erase.1 hb).1
    have hbs : b ∈ s.erase m := (mem_erase.1 hb).2
    rw [ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset hmem))
      (mem_erase.2 ⟨hba.symm, ha'⟩)]
    rw [show ((s.erase m).erase b).erase a = U.erase b from erase_right_comm]
  -- expand the right-hand side along the row of the least element `m`
  have Rr : ∀ c ∈ U, pfOn A ((s.erase a).erase c) = ∑ b ∈ U.erase c,
      (-1) ^ (rankIn ((s.erase a).erase c) b + 1) * A m b *
        pfOn A ((((s.erase a).erase c).erase m).erase b) := by
    intro c hc
    have hcm : c ≠ m := (mem_erase.1 (mem_erase.1 hc).2).1
    have hmac : m ∈ (s.erase a).erase c := mem_erase.2 ⟨hcm.symm, hm'⟩
    have hne' : ((s.erase a).erase c).Nonempty := ⟨m, hmac⟩
    rw [pfOn_eq_sum_min A hne',
      min'_eq_of_mem_subset hne hne' ((erase_subset _ _).trans (erase_subset _ _)) hmac]
    rw [show ((s.erase a).erase c).erase m = U.erase c by
      rw [erase_right_comm, hU', ]]
  rw [sum_congr rfl fun b hb => by rw [L b hb]]
  conv_rhs => rw [sum_congr rfl fun c hc => by rw [Rr c hc]]
  simp_rw [mul_sum]
  rw [sum_comm' (t' := U) (s' := fun c => U.erase c)]
  swap
  · intro x y
    simp only [mem_erase]
    tauto
  refine sum_congr rfl fun c hc => sum_congr rfl fun b hb => ?_
  have hbc : b ≠ c := (mem_erase.1 hb).1
  have hb : b ∈ U := (mem_erase.1 hb).2
  obtain ⟨hba, hbm, hbs⟩ : b ≠ a ∧ b ≠ m ∧ b ∈ s := by simpa [hU] using hb
  obtain ⟨hca, hcm, hcs⟩ : c ≠ a ∧ c ≠ m ∧ c ∈ s := by simpa [hU] using hc
  have hmb : m < b := lt_of_le_of_ne (min'_le s b hbs) (Ne.symm hbm)
  have hmc : m < c := lt_of_le_of_ne (min'_le s c hcs) (Ne.symm hcm)
  have hset : (((s.erase m).erase b).erase a).erase c = (((s.erase a).erase c).erase m).erase b := by
    ext x
    simp only [mem_erase]
    tauto
  rw [hset]
  -- the sign identity
  have h1 := rankIn_erase hmem a
  have h2 := rankIn_erase (mem_erase.2 ⟨hbm, hbs⟩) a
  have h3 := rankIn_erase hmem c
  have h4 := rankIn_erase (mem_erase.2 ⟨hbm, hbs⟩) c
  have h5 := rankIn_erase ha b
  have h6 := rankIn_erase (mem_erase.2 ⟨hca, hcs⟩) b
  have e1 := ltInd_add_ltInd hba
  have e2 := ltInd_add_ltInd hbc
  rw [ltInd_of_lt hma] at h1
  rw [ltInd_of_lt hmc] at h3
  have hsign : (-1 : R) ^ (rankIn s b + 1) * pairSign ((s.erase m).erase b) a c =
      pairSign s a c * (-1) ^ (rankIn ((s.erase a).erase c) b + 1) := by
    unfold pairSign
    rw [← pow_add, ← pow_add]
    apply neg_one_pow_eq_of_mod_two
    omega
  calc (-1 : R) ^ (rankIn s b + 1) * A m b *
        (pairSign ((s.erase m).erase b) a c * A a c * pfOn A ((((s.erase a).erase c).erase m).erase b))
      = ((-1 : R) ^ (rankIn s b + 1) * pairSign ((s.erase m).erase b) a c) * A a c * A m b *
          pfOn A ((((s.erase a).erase c).erase m).erase b) := by ring
    _ = _ := by rw [hsign]; ring

end Kasteleyn
