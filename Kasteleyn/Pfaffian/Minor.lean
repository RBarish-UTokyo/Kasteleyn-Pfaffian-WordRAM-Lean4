module

public import Kasteleyn.Pfaffian.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Minors of a matrix indexed by a linear order

For a square matrix `A` indexed by a linearly ordered type and finite sets of row indices `s`
and column indices `t` of the same cardinality, `Kasteleyn.minor A s t` is the determinant of
the submatrix of `A` on the rows `s` and the columns `t`, both listed in increasing order.

## Main results

* `Kasteleyn.minor_expand_row`, `Kasteleyn.minor_expand_col`: Laplace expansion of a minor
  along the row of an element `a ∈ s`, or along the column of an element `b ∈ t`, with the
  sign `(-1) ^ (rankIn s a + rankIn t b)`.
* `Kasteleyn.det_eq_zero_of_odd`: an alternating matrix (zero diagonal, skew-symmetric) of odd
  size has determinant zero, over any commutative ring.
* `Kasteleyn.minor_univ`: the full minor is the determinant.
-/

@[expose] public section

namespace Kasteleyn

open Finset Matrix

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-! ### Increasing enumerations of finite sets -/

lemma exists_orderEmbOfFin_eq {s : Finset ι} {k : ℕ} (h : #s = k) {a : ι} (ha : a ∈ s) :
    ∃ i, s.orderEmbOfFin h i = a := by
  have : a ∈ Set.range (s.orderEmbOfFin h) := by rw [range_orderEmbOfFin]; exact ha
  exact this

lemma rankIn_orderEmbOfFin (s : Finset ι) {k : ℕ} (h : #s = k) (i : Fin k) :
    rankIn s (s.orderEmbOfFin h i) = i := by
  unfold rankIn
  have : s.filter (· < s.orderEmbOfFin h i) =
      (Finset.Iio i).map (s.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [mem_filter, mem_map, mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨j, rfl⟩ := exists_orderEmbOfFin_eq h hx
      exact ⟨j, (s.orderEmbOfFin h).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, (s.orderEmbOfFin h).lt_iff_lt.2 hj⟩
  rw [this, card_map, Fin.card_Iio]

lemma card_erase_orderEmbOfFin (s : Finset ι) {k : ℕ} (h : #s = k + 1) (i : Fin (k + 1)) :
    #(s.erase (s.orderEmbOfFin h i)) = k := by
  rw [card_erase_of_mem (orderEmbOfFin_mem _ _ _), h]
  rfl

lemma orderEmbOfFin_comp_succAbove (s : Finset ι) {k : ℕ} (h : #s = k + 1) (i : Fin (k + 1)) :
    ⇑(s.orderEmbOfFin h) ∘ i.succAbove =
      (s.erase (s.orderEmbOfFin h i)).orderEmbOfFin (card_erase_orderEmbOfFin s h i) :=
  orderEmbOfFin_unique _
    (fun j => mem_erase.2 ⟨fun e => Fin.succAbove_ne i j ((s.orderEmbOfFin h).injective e),
      orderEmbOfFin_mem _ _ _⟩)
    ((s.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove i))

/-! ### Minors -/

/-- The minor of `A` with rows `s` and columns `t`, both listed in increasing order. By
convention it is `0` when `s` and `t` have different cardinalities. -/
def minor (A : Matrix ι ι R) (s t : Finset ι) : R :=
  if h : #t = #s then (A.submatrix (s.orderEmbOfFin rfl) (t.orderEmbOfFin h)).det else 0

variable (A : Matrix ι ι R)

lemma minor_eq {s t : Finset ι} {k : ℕ} (hs : #s = k) (ht : #t = k) :
    minor A s t = (A.submatrix (s.orderEmbOfFin hs) (t.orderEmbOfFin ht)).det := by
  subst hs
  simp [minor, ht]

@[simp] lemma minor_empty : minor A ∅ ∅ = 1 := by
  rw [minor_eq A (k := 0) rfl rfl]
  exact det_fin_zero

/-- Laplace expansion of a minor along the row of `a ∈ s`. -/
theorem minor_expand_row {s t : Finset ι} (hst : #s = #t) {a : ι} (ha : a ∈ s) :
    minor A s t = ∑ b ∈ t,
      (-1) ^ (rankIn s a + rankIn t b) * A a b * minor A (s.erase a) (t.erase b) := by
  obtain ⟨k, hk⟩ : ∃ k, #s = k + 1 := ⟨#s - 1, by have := card_pos.2 ⟨a, ha⟩; omega⟩
  have hk' : #t = k + 1 := hst ▸ hk
  obtain ⟨i, rfl⟩ := exists_orderEmbOfFin_eq hk ha
  have hsum := sum_map (univ : Finset (Fin (k + 1))) (t.orderEmbOfFin hk').toEmbedding
    (fun b => (-1 : R) ^ (rankIn s (s.orderEmbOfFin hk i) + rankIn t b) *
      A (s.orderEmbOfFin hk i) b * minor A (s.erase (s.orderEmbOfFin hk i)) (t.erase b))
  rw [map_orderEmbOfFin_univ] at hsum
  rw [minor_eq A hk hk', det_succ_row _ i, hsum]
  refine sum_congr rfl fun j _ => ?_
  simp only [RelEmbedding.coe_toEmbedding]
  rw [minor_eq A (card_erase_orderEmbOfFin s hk i) (card_erase_orderEmbOfFin t hk' j),
    rankIn_orderEmbOfFin, rankIn_orderEmbOfFin, submatrix_submatrix,
    orderEmbOfFin_comp_succAbove, orderEmbOfFin_comp_succAbove]
  rfl

/-- Laplace expansion of a minor along the column of `b ∈ t`. -/
theorem minor_expand_col {s t : Finset ι} (hst : #s = #t) {b : ι} (hb : b ∈ t) :
    minor A s t = ∑ a ∈ s,
      (-1) ^ (rankIn s a + rankIn t b) * A a b * minor A (s.erase a) (t.erase b) := by
  obtain ⟨k, hk'⟩ : ∃ k, #t = k + 1 := ⟨#t - 1, by have := card_pos.2 ⟨b, hb⟩; omega⟩
  have hk : #s = k + 1 := hst ▸ hk'
  obtain ⟨j, rfl⟩ := exists_orderEmbOfFin_eq hk' hb
  have hsum := sum_map (univ : Finset (Fin (k + 1))) (s.orderEmbOfFin hk).toEmbedding
    (fun a => (-1 : R) ^ (rankIn s a + rankIn t (t.orderEmbOfFin hk' j)) *
      A a (t.orderEmbOfFin hk' j) * minor A (s.erase a) (t.erase (t.orderEmbOfFin hk' j)))
  rw [map_orderEmbOfFin_univ] at hsum
  rw [minor_eq A hk hk', det_succ_column _ j, hsum]
  refine sum_congr rfl fun i _ => ?_
  simp only [RelEmbedding.coe_toEmbedding]
  rw [minor_eq A (card_erase_orderEmbOfFin s hk i) (card_erase_orderEmbOfFin t hk' j),
    rankIn_orderEmbOfFin, rankIn_orderEmbOfFin, submatrix_submatrix,
    orderEmbOfFin_comp_succAbove, orderEmbOfFin_comp_succAbove]
  rfl

/-- The full minor is the determinant. -/
theorem minor_univ [Fintype ι] : minor A univ univ = A.det := by
  rw [minor_eq A rfl rfl]
  have hbij : Function.Bijective ((univ : Finset ι).orderEmbOfFin rfl) := by
    refine ⟨(orderEmbOfFin _ _).injective, fun x => ?_⟩
    exact exists_orderEmbOfFin_eq rfl (mem_univ x)
  exact det_submatrix_equiv_self (Equiv.ofBijective _ hbij) A

/-! ### Alternating matrices of odd size -/

/-- An alternating matrix (zero diagonal, skew-symmetric) of odd size has determinant zero.
This holds over any commutative ring, including rings of characteristic two. -/
theorem det_eq_zero_of_odd {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n R}
    (hd : ∀ i, M i i = 0) (hM : ∀ i j, M j i = -M i j) (hn : Odd (Fintype.card n)) :
    M.det = 0 := by
  rw [det_apply]
  refine sum_involution (fun σ _ => σ⁻¹) (fun σ _ => ?_) (fun σ _ hne heq => ?_)
    (fun _ _ => mem_univ _) (fun σ _ => inv_inv σ)
  · have hprod : ∏ i, M (σ⁻¹ i) i = -∏ i, M (σ i) i := by
      rw [← Equiv.prod_comp σ (fun i => M (σ⁻¹ i) i)]
      have hinv : ∀ i, σ⁻¹ (σ i) = i := fun i => σ.symm_apply_apply i
      simp only [hinv]
      rw [show (fun i => M i (σ i)) = fun i => -M (σ i) i from funext fun i => hM _ _,
        prod_neg, card_univ, hn.neg_one_pow, neg_one_mul]
    rw [Equiv.Perm.sign_inv, hprod, smul_neg, add_neg_cancel]
  · apply hne
    have hσ : σ ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      nth_rewrite 1 [← heq]
      exact inv_mul_cancel σ
    obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
      (by have := Nat.odd_iff.1 hn; omega) hσ
    rw [prod_eq_zero (mem_univ a) (by rw [ha, hd]), smul_zero]

theorem minor_self_eq_zero_of_odd {A : Matrix ι ι R} (hd : ∀ i, A i i = 0)
    (hA : ∀ i j, A j i = -A i j) {s : Finset ι} (hs : Odd #s) : minor A s s = 0 := by
  rw [minor_eq A rfl rfl]
  exact det_eq_zero_of_odd (fun i => hd _) (fun i j => hA _ _) (by simpa using hs)

end Kasteleyn
