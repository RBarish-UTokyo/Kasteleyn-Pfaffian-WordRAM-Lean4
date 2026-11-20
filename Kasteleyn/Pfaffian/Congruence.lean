module

public import Kasteleyn.Pfaffian.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# The Pfaffian of a congruent matrix

For an alternating matrix `A` (zero diagonal and `A j i = -A i j`) and any square matrix `B`
over a commutative ring, `pf (Bᵀ * A * B) = det B * pf A`.

The proof shows that `v ↦ pf (Gram matrix of the vectors v for A)` is an alternating
multilinear form in the vectors `v`, so it is a multiple of the determinant; the multilinearity
comes from the expansion of the Pfaffian along a row, and the alternating property from the
vanishing of the Pfaffian of a skew-symmetric matrix with two equal rows.

## Main results

* `Kasteleyn.pfOn_congr`: `pfOn A s` only depends on the entries of `A` in `s × s`.
* `Kasteleyn.pfOn_eq_zero_of_row_eq`: a Pfaffian with two equal rows vanishes.
* `Kasteleyn.pf_transpose_mul_mul`: `pf (Bᵀ * A * B) = det B * pf A`.
-/

@[expose] public section

namespace Kasteleyn

open Finset Matrix

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

lemma neg_one_pow_add_neg_one_pow {m n : ℕ} (h : (m + n) % 2 = 1) :
    (-1 : R) ^ m + (-1) ^ n = 0 := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n)]
  rcases (by omega : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring

/-- The Pfaffian of a principal submatrix only depends on the entries of that submatrix. -/
theorem pfOn_congr {A A' : Matrix ι ι R} {s : Finset ι}
    (h : ∀ i ∈ s, ∀ j ∈ s, A i j = A' i j) : pfOn A s = pfOn A' s := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hm := min'_mem s hne
  rw [pfOn_eq_sum_min A hne, pfOn_eq_sum_min A' hne]
  refine sum_congr rfl fun b hb => ?_
  have hsub : (s.erase (s.min' hne)).erase b ⊆ s := (erase_subset _ _).trans (erase_subset _ _)
  rw [h _ hm _ (mem_of_mem_erase hb), ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset hm))
    fun i hi j hj => h i (hsub hi) j (hsub hj)]

/-- The Pfaffian of a skew-symmetric matrix with two equal rows `x ≠ y` (and `A x y = 0`)
vanishes. This holds over any commutative ring. -/
theorem pfOn_eq_zero_of_row_eq {A : Matrix ι ι R} (hA : ∀ i j, A j i = -A i j) {s : Finset ι}
    {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hrow : ∀ j ∈ s, A x j = A y j)
    (hzero : A x y = 0) : pfOn A s = 0 := by
  have hy' : y ∈ s.erase x := mem_erase.2 ⟨hxy.symm, hy⟩
  rw [pfOn_expand hA hx, ← add_sum_erase _ _ hy', hzero, mul_zero, zero_mul, zero_add]
  set U := (s.erase x).erase y with hU
  -- expand each remaining Pfaffian along the row `y`
  have hexp : ∀ b ∈ U, pfOn A ((s.erase x).erase b) = ∑ c ∈ U.erase b,
      pairSign ((s.erase x).erase b) y c * A x c *
        pfOn A ((((s.erase x).erase b).erase y).erase c) := by
    intro b hb
    obtain ⟨hby, hbx, -⟩ : b ≠ y ∧ b ≠ x ∧ b ∈ s := by simpa [hU] using hb
    rw [pfOn_expand hA (mem_erase.2 ⟨hby.symm, hy'⟩),
      show ((s.erase x).erase b).erase y = U.erase b from erase_right_comm]
    refine sum_congr rfl fun c hc => ?_
    rw [hrow c (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase hc)))]
  rw [sum_congr rfl fun b hb => by rw [hexp b hb]]
  simp_rw [mul_sum]
  rw [← sum_finset_product' U.offDiag U (fun b => U.erase b)
    (fun p => by simp only [mem_offDiag, mem_erase]; tauto)]
  refine sum_involution (fun p _ => (p.2, p.1)) (fun p hp => ?_) (fun p hp _ h => ?_)
    (fun p hp => by simp only [mem_offDiag] at hp ⊢; tauto) (fun p _ => rfl)
  · obtain ⟨hb, hc, hbc⟩ := mem_offDiag.1 hp
    obtain ⟨hby, hbx, hbs⟩ : p.1 ≠ y ∧ p.1 ≠ x ∧ p.1 ∈ s := by simpa [hU] using hb
    obtain ⟨hcy, hcx, hcs⟩ : p.2 ≠ y ∧ p.2 ≠ x ∧ p.2 ∈ s := by simpa [hU] using hc
    have hset : (((s.erase x).erase p.1).erase y).erase p.2 =
        (((s.erase x).erase p.2).erase y).erase p.1 := by
      ext z
      simp only [mem_erase]
      tauto
    rw [hset]
    have h1 := rankIn_erase hx p.1
    have h2 := rankIn_erase hx p.2
    have h3 := rankIn_erase hx y
    have h4 := rankIn_erase (mem_erase.2 ⟨hbx, hbs⟩) y
    have h5 := rankIn_erase (mem_erase.2 ⟨hbx, hbs⟩) p.2
    have h6 := rankIn_erase (mem_erase.2 ⟨hcx, hcs⟩) y
    have h7 := rankIn_erase (mem_erase.2 ⟨hcx, hcs⟩) p.1
    have e1 := ltInd_add_ltInd hbc
    have e2 := ltInd_add_ltInd hby
    have e3 := ltInd_add_ltInd hcy
    have hsign : pairSign s x p.1 * pairSign ((s.erase x).erase p.1) y p.2 +
        (pairSign s x p.2 * pairSign ((s.erase x).erase p.2) y p.1 : R) = 0 := by
      unfold pairSign
      rw [← pow_add, ← pow_add]
      apply neg_one_pow_add_neg_one_pow
      omega
    calc pairSign s x p.1 * A x p.1 *
          (pairSign ((s.erase x).erase p.1) y p.2 * A x p.2 *
            pfOn A ((((s.erase x).erase p.2).erase y).erase p.1)) +
        pairSign s x p.2 * A x p.2 *
          (pairSign ((s.erase x).erase p.2) y p.1 * A x p.1 *
            pfOn A ((((s.erase x).erase p.2).erase y).erase p.1))
        = (pairSign s x p.1 * pairSign ((s.erase x).erase p.1) y p.2 +
            pairSign s x p.2 * pairSign ((s.erase x).erase p.2) y p.1) *
          (A x p.1 * A x p.2 * pfOn A ((((s.erase x).erase p.2).erase y).erase p.1)) := by ring
      _ = 0 := by rw [hsign, zero_mul]
  · exact (mem_offDiag.1 hp).2.2 (Prod.ext_iff.1 h).2

/-! ### Gram matrices -/

variable [Fintype ι]

/-- The Gram matrix of the vectors `v i` for the bilinear form with matrix `A`. -/
def gram (A : Matrix ι ι R) (v : ι → ι → R) : Matrix ι ι R :=
  Matrix.of fun i j => ∑ k, ∑ l, v i k * A k l * v j l

omit [LinearOrder ι] in
lemma gram_apply (A : Matrix ι ι R) (v : ι → ι → R) (i j : ι) :
    gram A v i j = ∑ k, ∑ l, v i k * A k l * v j l := rfl

omit [LinearOrder ι] in
lemma gram_skew {A : Matrix ι ι R} (hA : ∀ i j, A j i = -A i j) (v : ι → ι → R) (i j : ι) :
    gram A v j i = -gram A v i j := by
  rw [gram_apply, gram_apply, sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [hA]
  ring

omit [LinearOrder ι] in
/-- The quadratic form of an alternating matrix vanishes identically. -/
lemma sum_sum_alternating {A : Matrix ι ι R} (hd : ∀ i, A i i = 0)
    (hA : ∀ i j, A j i = -A i j) (c : ι → R) : ∑ k, ∑ l, c k * A k l * c l = 0 := by
  rw [← sum_product']
  refine sum_involution (fun p _ => (p.2, p.1)) (fun p _ => ?_) (fun p _ hne h => ?_)
    (fun p _ => mem_product.2 ⟨mem_univ _, mem_univ _⟩) (fun p _ => rfl)
  · rw [hA]
    ring
  · apply hne
    have : p.1 = p.2 := (Prod.ext_iff.1 h).2
    rw [this, hd, mul_zero, zero_mul]

lemma pf_gram_update {A : Matrix ι ι R} (hA : ∀ i j, A j i = -A i j) (v : ι → ι → R) (x : ι)
    (w : ι → R) :
    pf (gram A (Function.update v x w)) = ∑ b ∈ univ.erase x,
      pairSign univ x b * (∑ k, ∑ l, w k * A k l * v b l) *
        pfOn (gram A v) ((univ.erase x).erase b) := by
  rw [pf_def, pfOn_expand (gram_skew hA _) (mem_univ x)]
  refine sum_congr rfl fun b hb => ?_
  have hbx : b ≠ x := ne_of_mem_erase hb
  rw [gram_apply, Function.update_self, Function.update_of_ne hbx]
  congr 1
  refine pfOn_congr fun i hi j hj => ?_
  obtain ⟨-, hix, -⟩ : i ≠ b ∧ i ≠ x ∧ True := by simpa using hi
  obtain ⟨-, hjx, -⟩ : j ≠ b ∧ j ≠ x ∧ True := by simpa using hj
  rw [gram_apply, gram_apply, Function.update_of_ne hix, Function.update_of_ne hjx]

/-- For an alternating matrix `A`, the Pfaffian of the Gram matrix is an alternating
multilinear form in the vectors. -/
def pfGram {A : Matrix ι ι R} (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j) :
    (ι → R) [⋀^ι]→ₗ[R] R where
  toFun v := pf (gram A v)
  map_update_add' := by
    intro inst v x u w
    obtain rfl : inst = LinearOrder.toDecidableEq := Subsingleton.elim _ _
    simp only [pf_gram_update hA, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, add_mul, sum_add_distrib]
    ring
  map_update_smul' := by
    intro inst v x c w
    obtain rfl : inst = LinearOrder.toDecidableEq := Subsingleton.elim _ _
    rw [pf_gram_update hA, pf_gram_update hA, smul_eq_mul, Finset.mul_sum (s := univ.erase x)]
    refine sum_congr rfl fun b _ => ?_
    have : ∑ k, ∑ l, (c • w) k * A k l * v b l = c * ∑ k, ∑ l, w k * A k l * v b l := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
    rw [this]
    ring
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    refine pfOn_eq_zero_of_row_eq (gram_skew hA v) (mem_univ i) (mem_univ j) hne
      (fun b _ => by rw [gram_apply, gram_apply, hij]) ?_
    rw [gram_apply, hij]
    exact sum_sum_alternating hd hA (v j)

lemma pfGram_apply {A : Matrix ι ι R} (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j)
    (v : ι → ι → R) : pfGram hd hA v = pf (gram A v) := rfl

/-- **The Pfaffian of a congruent matrix**: for an alternating matrix `A` and any `B`,
`pf (Bᵀ * A * B) = det B * pf A`. -/
theorem pf_transpose_mul_mul {A : Matrix ι ι R} (hd : ∀ i, A i i = 0)
    (hA : ∀ i j, A j i = -A i j) (B : Matrix ι ι R) : pf (Bᵀ * A * B) = B.det * pf A := by
  have key := congrArg (fun f => f (fun x k => B k x))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun R ι) (pfGram hd hA))
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Pi.basisFun_det_apply, pfGram_apply] at key
  have h1 : gram A (fun x k => B k x) = Bᵀ * A * B := by
    ext i j
    simp only [gram_apply, mul_apply, transpose_apply, sum_mul]
    rw [sum_comm]
  have h2 : gram A (Pi.basisFun R ι) = A := by
    ext i j
    simp [gram_apply, Pi.single_apply]
  have h3 : Matrix.of (fun x k => B k x) = Bᵀ := rfl
  rw [h1, h2, h3, det_transpose] at key
  rw [key, mul_comm]

end Kasteleyn
