module

public import Kasteleyn.Pfaffian.Matching
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Sum.Order

/-!
# Elementary properties of the Pfaffian

* `Kasteleyn.pf_fin_two`: the Pfaffian of a `2 × 2` matrix is its upper right entry.
* `Kasteleyn.pf_eq_zero_of_odd`: the Pfaffian of a matrix of odd size vanishes.
* `Kasteleyn.pfOn_submatrix_of_strictMono`: the Pfaffian is invariant under an increasing
  relabelling of the indices.
* `Kasteleyn.pfOn_union_of_lt`, `Kasteleyn.pf_fromBlocks_zero`: the Pfaffian of a block-diagonal
  matrix (with the blocks in increasing order) is the product of the Pfaffians of the blocks.
* `Kasteleyn.pfOn_eq_sum_of_support`, `Kasteleyn.pf_eq_sum_of_adj`: if the entries of `A` vanish
  outside the edges of a graph `G`, then the Pfaffian of `A` is the signed sum over the perfect
  matchings of `G` of the products of the matched entries. This applies in particular to the
  signed (weighted) adjacency matrix of an oriented graph, the matrix used in Kasteleyn's method
  for counting perfect matchings.

## References

* P. W. Kasteleyn, *The statistics of dimers on a lattice*, Physica 27 (1961), 1209–1225.
* P. W. Kasteleyn, *Graph theory and crystal physics*, in *Graph Theory and Theoretical Physics*,
  Academic Press (1967), 43–110.
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.3.
-/

@[expose] public section

namespace Kasteleyn

open Finset Matrix

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-! ### Small and odd matrices -/

/-- The Pfaffian of a `2 × 2` matrix is its upper right entry. -/
theorem pf_fin_two (a b c d : R) : pf !![a, b; c, d] = b := by
  rw [pf_def, show (univ : Finset (Fin 2)) = {0, 1} by decide,
    pfOn_pair _ (show (0 : Fin 2) < 1 by decide)]
  rfl

/-- The Pfaffian of a matrix of odd size vanishes. -/
theorem pf_eq_zero_of_odd [Fintype ι] (A : Matrix ι ι R) (h : Odd (Fintype.card ι)) :
    pf A = 0 :=
  pfOn_eq_zero_of_odd A (by simpa using h)

/-! ### Increasing relabelling -/

lemma rankIn_image {κ : Type*} [LinearOrder κ] {f : κ → ι} (hf : StrictMono f) (s : Finset κ)
    (x : κ) : rankIn (s.image f) (f x) = rankIn s x := by
  unfold rankIn
  rw [filter_image, card_image_of_injective _ hf.injective]
  congr 1
  exact filter_congr fun y _ => hf.lt_iff_lt

/-- The Pfaffian is invariant under an increasing relabelling of the indices. -/
theorem pfOn_submatrix_of_strictMono {κ : Type*} [LinearOrder κ] (A : Matrix ι ι R)
    {f : κ → ι} (hf : StrictMono f) (s : Finset κ) :
    pfOn (A.submatrix f f) s = pfOn A (s.image f) := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hne' : (s.image f).Nonempty := hne.image f
  rw [pfOn_eq_sum_min _ hne, pfOn_eq_sum_min A hne', min'_image hf.monotone,
    ← image_erase hf.injective, sum_image hf.injective.injOn]
  refine sum_congr rfl fun b hb => ?_
  rw [ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset (min'_mem s hne))),
    rankIn_image hf, image_erase hf.injective, image_erase hf.injective]
  rfl

/-! ### Block-diagonal matrices -/

/-- If every element of `s` is smaller than every element of `t` and the entries of `A` between
`s` and `t` vanish, then the Pfaffian of `A` on `s ∪ t` is the product of the Pfaffians. -/
theorem pfOn_union_of_lt (A : Matrix ι ι R) {s t : Finset ι} (hlt : ∀ x ∈ s, ∀ y ∈ t, x < y)
    (hz : ∀ x ∈ s, ∀ y ∈ t, A x y = 0) : pfOn A (s ∪ t) = pfOn A s * pfOn A t := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨m, hm⟩ : ∃ m, s.min' hne = m := ⟨_, rfl⟩
  have hms : m ∈ s := hm ▸ min'_mem s hne
  have hmt : m ∉ t := fun h => lt_irrefl m (hlt m hms m h)
  have hne' : (s ∪ t).Nonempty := hne.mono subset_union_left
  have hmin' : (s ∪ t).min' hne' = m := by
    refine le_antisymm (min'_le _ _ (mem_union_left _ hms)) (le_min' _ _ _ fun x hx => ?_)
    rcases mem_union.1 hx with hx | hx
    · exact hm ▸ min'_le s x hx
    · exact (hlt m hms x hx).le
  rw [pfOn_eq_sum_min A hne', pfOn_eq_sum_min A hne, hmin', hm, sum_mul,
    show (s ∪ t).erase m = s.erase m ∪ t by
      rw [erase_union_distrib, erase_eq_of_notMem hmt],
    sum_union (disjoint_left.2 fun x hx hxt => lt_irrefl x (hlt x (mem_of_mem_erase hx) x hxt)),
    sum_eq_zero (s := t) fun b hb => by rw [hz m hms b hb, mul_zero, zero_mul], add_zero]
  refine sum_congr rfl fun b hb => ?_
  have hbs : b ∈ s := mem_of_mem_erase hb
  have hbt : b ∉ t := fun h => lt_irrefl b (hlt b hbs b h)
  have hsub : (s.erase m).erase b ⊂ s :=
    (erase_subset _ _).trans_ssubset (erase_ssubset hms)
  rw [show ((s.erase m ∪ t).erase b) = (s.erase m).erase b ∪ t by
      rw [erase_union_distrib, erase_eq_of_notMem hbt],
    ih _ hsub (fun x hx => hlt x (hsub.subset hx)) (fun x hx => hz x (hsub.subset hx))]
  have hrank : rankIn (s ∪ t) b = rankIn s b := by
    unfold rankIn
    rw [filter_union, filter_eq_empty_iff.2 fun y hy hyb => lt_asymm hyb (hlt b hbs y hy),
      union_empty]
  rw [hrank]
  ring

/-- The Pfaffian of a block-diagonal matrix, with the index set ordered lexicographically
(first block before second block), is the product of the Pfaffians of the blocks. -/
theorem pf_fromBlocks_zero {n o : Type*} [Fintype n] [Fintype o] [LinearOrder n] [LinearOrder o]
    (A : Matrix n n R) (B : Matrix o o R) :
    pf ((fromBlocks A 0 0 B).submatrix ofLex ofLex : Matrix (n ⊕ₗ o) (n ⊕ₗ o) R) =
      pf A * pf B := by
  have h := pfOn_union_of_lt ((fromBlocks A 0 0 B).submatrix ofLex ofLex)
    (s := univ.image (toLex ∘ Sum.inl)) (t := univ.image (toLex ∘ Sum.inr))
    (by
      simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact Sum.Lex.inl_lt_inr i j)
    (by
      simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rfl)
  rw [pf_def ((fromBlocks A 0 0 B).submatrix ofLex ofLex)]
  convert h using 2
  · ext x
    obtain ⟨y, rfl⟩ := toLex.surjective x
    rcases y with i | i
    · exact iff_of_true (mem_univ _) (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
    · exact iff_of_true (mem_univ _) (mem_union_right _ (mem_image_of_mem _ (mem_univ i)))
  · have e := pfOn_submatrix_of_strictMono
      ((fromBlocks A 0 0 B).submatrix ofLex ofLex : Matrix (n ⊕ₗ o) (n ⊕ₗ o) R)
      (Sum.Lex.inl_strictMono (α := n) (β := o)) univ
    exact Eq.trans rfl (e.trans (by congr 1))
  · have e := pfOn_submatrix_of_strictMono
      ((fromBlocks A 0 0 B).submatrix ofLex ofLex : Matrix (n ⊕ₗ o) (n ⊕ₗ o) R)
      (Sum.Lex.inr_strictMono (α := n) (β := o)) univ
    exact Eq.trans rfl (e.trans (by congr 1))

/-! ### Matrices supported on the edges of a graph -/

variable [Fintype ι]

/-- If the entries `A x y` with `x < y` vanish unless `E x y`, then only the perfect matchings
all of whose pairs satisfy `E` contribute to the Pfaffian. -/
theorem pfOn_eq_sum_of_support (A : Matrix ι ι R) (s : Finset ι) (E : ι → ι → Prop)
    [DecidableRel E] (hA : ∀ x y, x < y → ¬E x y → A x y = 0) :
    pfOn A s = ∑ μ ∈ (perfectMatchingsOn s).filter (fun μ => ∀ x ∈ s, x < μ x → E x (μ x)),
      (-1) ^ crossingNumber s μ * matchingWeight A s μ := by
  rw [pfOn_eq_sum_perfectMatchingsOn, sum_filter_of_ne]
  intro μ _ hne x hx hlt
  by_contra hE
  apply hne
  rw [matchingWeight, prod_eq_zero (mem_filter.2 ⟨hx, hlt⟩) (hA x (μ x) hlt hE), mul_zero]

/-- **The Pfaffian of a matrix supported on the edges of a graph** (for instance the signed,
weighted adjacency matrix of an oriented graph) is the signed sum, over the perfect matchings `μ`
of the graph, of the products of the matched entries `A x (μ x)` with `x < μ x`; the sign is
`(-1)` to the crossing number of `μ`. -/
theorem pf_eq_sum_of_adj (G : SimpleGraph ι) [DecidableRel G.Adj] (A : Matrix ι ι R)
    (hA : ∀ x y, ¬G.Adj x y → A x y = 0) :
    pf A = ∑ μ ∈ (perfectMatchingsOn (univ : Finset ι)).filter (fun μ => ∀ x, G.Adj x (μ x)),
      (-1) ^ crossingNumber univ μ * matchingWeight A univ μ := by
  rw [pf_def, pfOn_eq_sum_of_support A univ G.Adj fun x y _ h => hA x y h]
  congr 1
  refine filter_congr fun μ hμ => ?_
  rw [mem_perfectMatchingsOn] at hμ
  refine ⟨fun h x => ?_, fun h x _ _ => h x⟩
  rcases (hμ.apply_ne (mem_univ x)).lt_or_gt with hlt | hlt
  · have := h (μ x) (mem_univ _)
    rw [hμ.apply_apply] at this
    exact (this hlt).symm
  · exact h x (mem_univ x) hlt

end Kasteleyn
