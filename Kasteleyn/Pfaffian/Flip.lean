module

public import Kasteleyn.Pfaffian.Congruence
public import Mathlib.Tactic.LinearCombination

/-!
# The Pfaffian sign of a matching and alternating cycles

Fix a function `σ : ι → ι → R` with `σ y x = -σ x y` and `σ x y ^ 2 = 1` for `x ≠ y` (a sign on
every ordered pair, such as `±1` according to an orientation). For a perfect matching `m` of a
finite set `s ⊆ ι` (given as a function which is an involution without fixed points on `s`), the
matrix `matchingMatrix σ s m` has the entries `σ x (m x)` for `x ∈ s`, and zeros elsewhere. Its
Pfaffian `pfOn (matchingMatrix σ s m) s` is the signed term of `m` in the expansion of a Pfaffian
as a sum over perfect matchings; it is `±1`.

The main result, `Kasteleyn.pfOn_matchingMatrix_mul_flip`, compares two perfect matchings `m`,
`m'` of `s` which differ along a single alternating cycle `x₀ x₁ x₂ … x₂ₖ₋₁` (with
`m x₂ᵢ = x₂ᵢ₊₁` and `m' x₂ᵢ₊₁ = x₂ᵢ₊₂`, indices modulo `2k`) and agree elsewhere: the product of
their terms is `-∏ σ xᵢ xᵢ₊₁`, the product running around the cycle. The proof is by induction
on the length of the cycle, expanding the Pfaffians along rows of the cycle.

The cycle is given as the list of pairs `(x₂ᵢ, x₂ᵢ₊₁)`.

## References

* P. W. Kasteleyn, *Dimer statistics and phase transitions*, J. Math. Phys. 4 (1963), 287–293.
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.3.
-/

@[expose] public section

namespace Kasteleyn

open Finset

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

/-- `m` is a perfect matching of `s`: it maps `s` to itself, without fixed points, and is an
involution on `s`. -/
def IsMatchingOn (s : Finset ι) (m : ι → ι) : Prop := ∀ x ∈ s, m x ∈ s ∧ m x ≠ x ∧ m (m x) = x

/-- The matrix of a perfect matching `m` of `s`, with the entries `σ x (m x)` for `x ∈ s`. -/
def matchingMatrix (σ : ι → ι → R) (s : Finset ι) (m : ι → ι) : Matrix ι ι R :=
  fun x y => if x ∈ s ∧ m x = y then σ x y else 0

variable {σ : ι → ι → R} {s : Finset ι} {m m' : ι → ι}

lemma IsMatchingOn.erase_erase (hm : IsMatchingOn s m) {a : ι} (ha : a ∈ s) :
    IsMatchingOn ((s.erase a).erase (m a)) m := by
  intro x hx
  obtain ⟨hxa', hxa, hxs⟩ : x ≠ m a ∧ x ≠ a ∧ x ∈ s := by simpa using hx
  obtain ⟨h1, h2, h3⟩ := hm x hxs
  refine ⟨?_, h2, h3⟩
  simp only [mem_erase]
  refine ⟨fun h => hxa ?_, fun h => hxa' ?_, h1⟩
  · rw [← h3, h, (hm a ha).2.2]
  · rw [← h3, h]

lemma matchingMatrix_antisymm (hσ : ∀ x y, x ≠ y → σ y x = -σ x y) (hm : IsMatchingOn s m)
    (i j : ι) : matchingMatrix σ s m j i = -matchingMatrix σ s m i j := by
  unfold matchingMatrix
  by_cases h : i ∈ s ∧ m i = j
  · obtain ⟨hi, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := hm i hi
    rw [ite_eq_left ⟨h1, h3⟩, ite_eq_left ⟨hi, rfl⟩, hσ _ _ h2.symm]
  · rw [ite_eq_right h, neg_zero, ite_eq_right]
    rintro ⟨hj, rfl⟩
    exact h ⟨(hm j hj).1, (hm j hj).2.2⟩

/-- Expansion of the Pfaffian of a matching along the row `a`. -/
lemma pfOn_matchingMatrix_expand (hσ : ∀ x y, x ≠ y → σ y x = -σ x y) (hm : IsMatchingOn s m)
    {a : ι} (ha : a ∈ s) :
    pfOn (matchingMatrix σ s m) s = pairSign s a (m a) * σ a (m a) *
      pfOn (matchingMatrix σ ((s.erase a).erase (m a)) m) ((s.erase a).erase (m a)) := by
  rw [pfOn_expand (matchingMatrix_antisymm hσ hm) ha,
    sum_eq_single_of_mem (m a) (mem_erase.2 ⟨(hm a ha).2.1, (hm a ha).1⟩)]
  · congr 1
    · simp [matchingMatrix, ha]
    · refine pfOn_congr fun i hi j _ => ?_
      have : i ∈ s := mem_of_mem_erase (mem_of_mem_erase hi)
      simp [matchingMatrix, hi, this]
  · intro b _ hb
    simp [matchingMatrix, ha, Ne.symm hb]

lemma pairSign_mul_self (t : Finset ι) (a b : ι) : pairSign t a b * pairSign t a b = (1 : R) := by
  unfold pairSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- The term of a perfect matching is a sign. -/
lemma pfOn_matchingMatrix_mul_self (hσ : ∀ x y, x ≠ y → σ y x = -σ x y)
    (hσ1 : ∀ x y, x ≠ y → σ x y * σ x y = 1) (hm : IsMatchingOn s m) :
    pfOn (matchingMatrix σ s m) s * pfOn (matchingMatrix σ s m) s = 1 := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  rw [pfOn_matchingMatrix_expand hσ hm ha]
  have := ih _ ((erase_subset _ _).trans_ssubset (erase_ssubset ha)) (hm.erase_erase ha)
  have h2 := hσ1 a (m a) (hm a ha).2.1.symm
  have h3 := pairSign_mul_self (R := R) s a (m a)
  linear_combination (pairSign s a (m a) * pairSign s a (m a) * (σ a (m a) * σ a (m a))) * this +
    pairSign s a (m a) * pairSign s a (m a) * h2 + h3

/-! ### Alternating cycles -/

/-- The first entry of the head of a list of pairs, or `a₀` for the empty list. -/
def nextFst (a₀ : ι) : List (ι × ι) → ι
  | [] => a₀
  | p :: _ => p.1

omit [LinearOrder ι] in
@[simp] lemma nextFst_nil (a₀ : ι) : nextFst a₀ [] = a₀ := rfl

omit [LinearOrder ι] in
@[simp] lemma nextFst_cons (a₀ : ι) (p : ι × ι) (l : List (ι × ι)) :
    nextFst a₀ (p :: l) = p.1 := rfl

/-- The vertices of a list of pairs. -/
def pairVerts (l : List (ι × ι)) : List ι := l.flatMap fun p => [p.1, p.2]

omit [LinearOrder ι] in
@[simp] lemma pairVerts_nil : pairVerts ([] : List (ι × ι)) = [] := rfl

omit [LinearOrder ι] in
@[simp] lemma pairVerts_cons (p : ι × ι) (l : List (ι × ι)) :
    pairVerts (p :: l) = p.1 :: p.2 :: pairVerts l := rfl

/-- `m'` links each pair to the next one, and the last pair to `a₀`: the list of pairs
`(x₀, x₁), (x₂, x₃), …` with `a₀ = x₀` describes the cycle `x₀ x₁ x₂ x₃ …` alternating between
the pairs of `m` (inside the list entries) and those of `m'` (between them). -/
def AltChain (m' : ι → ι) (a₀ : ι) : List (ι × ι) → Prop
  | [] => True
  | p :: l => m' p.2 = nextFst a₀ l ∧ AltChain m' a₀ l

/-- The product of `σ` around the cycle described by a list of pairs. -/
def altProd (σ : ι → ι → R) (a₀ : ι) : List (ι × ι) → R
  | [] => 1
  | p :: l => σ p.1 p.2 * σ p.2 (nextFst a₀ l) * altProd σ a₀ l

omit [LinearOrder ι] in
@[simp] lemma altChain_nil (a₀ : ι) : AltChain m' a₀ [] := trivial

omit [LinearOrder ι] in
@[simp] lemma altChain_cons (a₀ : ι) (p : ι × ι) (l : List (ι × ι)) :
    AltChain m' a₀ (p :: l) ↔ m' p.2 = nextFst a₀ l ∧ AltChain m' a₀ l := Iff.rfl

omit [LinearOrder ι] in
@[simp] lemma altProd_nil (a₀ : ι) : altProd σ a₀ [] = 1 := rfl

omit [LinearOrder ι] in
@[simp] lemma altProd_cons (a₀ : ι) (p : ι × ι) (l : List (ι × ι)) :
    altProd σ a₀ (p :: l) = σ p.1 p.2 * σ p.2 (nextFst a₀ l) * altProd σ a₀ l := rfl

omit [LinearOrder ι] in
lemma pairVerts_map {κ : Type*} (g : κ → ι × ι) (l : List κ) :
    pairVerts (l.map g) = l.flatMap fun i => [(g i).1, (g i).2] := by
  simp [pairVerts, List.flatMap_map]

/-- The sign identity behind the flip lemma. -/
lemma pairSign_flip {x₀ x₁ x₂ x₃ : ι} (h₁ : x₁ ∈ s) (h₀ : x₀ ∈ s.erase x₁)
    (h₂ : x₂ ∈ s.erase x₁) (h02 : x₀ ≠ x₂) :
    pairSign s x₁ x₀ * pairSign ((s.erase x₁).erase x₀) x₂ x₃ *
      pairSign ((s.erase x₁).erase x₂) x₀ x₃ * pairSign s x₁ x₂ = (-1 : R) := by
  unfold pairSign
  rw [← pow_add, ← pow_add, ← pow_add]
  apply Odd.neg_one_pow
  rw [Nat.odd_iff]
  have e0 := rankIn_erase h₁ x₀
  have e2 := rankIn_erase h₁ x₂
  have e1 := rankIn_erase h₁ x₁
  have f2 := rankIn_erase h₀ x₂
  have f3 := rankIn_erase h₀ x₃
  have g0 := rankIn_erase h₂ x₀
  have g3 := rankIn_erase h₂ x₃
  have l1 := ltInd_add_ltInd h02
  omega

/-- **The flip lemma.** Let `m` and `m'` be perfect matchings of `s` which agree outside the
cycle `x₀ x₁ x₂ … x₂ₖ₋₁`, described by the list of pairs `(x₀, x₁) :: l`, with
`m x₂ᵢ = x₂ᵢ₊₁` and `m' x₂ᵢ₊₁ = x₂ᵢ₊₂` (indices modulo `2k`). Then the product of the terms of
`m` and `m'` is `-∏ σ xᵢ xᵢ₊₁`, the product running around the cycle. -/
theorem pfOn_matchingMatrix_mul_flip (hσ : ∀ x y, x ≠ y → σ y x = -σ x y)
    (hσ1 : ∀ x y, x ≠ y → σ x y * σ x y = 1) (x₀ x₁ : ι) (l : List (ι × ι))
    (hm : IsMatchingOn s m) (hm' : IsMatchingOn s m')
    (hnd : (pairVerts ((x₀, x₁) :: l)).Nodup) (hsub : ∀ x ∈ pairVerts ((x₀, x₁) :: l), x ∈ s)
    (h1 : ∀ p ∈ (x₀, x₁) :: l, m p.1 = p.2) (h2 : AltChain m' x₀ ((x₀, x₁) :: l))
    (hagree : ∀ x ∈ s, x ∉ pairVerts ((x₀, x₁) :: l) → m x = m' x) :
    pfOn (matchingMatrix σ s m) s * pfOn (matchingMatrix σ s m') s =
      -altProd σ x₀ ((x₀, x₁) :: l) := by
  induction l generalizing s m x₁ with
  | nil =>
    have h01 : x₀ ≠ x₁ := fun h => by simp [h] at hnd
    simp only [pairVerts_cons, pairVerts_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hsub hagree
    have hx₀ : x₀ ∈ s := hsub x₀ (Or.inl rfl)
    have hx₁ : x₁ ∈ s := hsub x₁ (Or.inr rfl)
    have hm0 : m x₀ = x₁ := h1 _ (List.mem_cons_self ..)
    have hm'1 : m' x₁ = x₀ := h2.1
    have heq : matchingMatrix σ s m' = matchingMatrix σ s m := by
      funext x y
      unfold matchingMatrix
      by_cases hx : x ∈ s
      · have : m' x = m x := by
          by_cases e0 : x = x₀
          · rw [e0, hm0, ← hm'1, (hm' x₁ hx₁).2.2]
          by_cases e1 : x = x₁
          · rw [e1, hm'1, ← hm0, (hm x₀ hx₀).2.2]
          exact (hagree x hx (by tauto)).symm
        rw [this]
      · simp [hx]
    rw [heq, pfOn_matchingMatrix_mul_self hσ hσ1 hm]
    simp only [altProd, nextFst, mul_one]
    rw [hσ x₀ x₁ h01, mul_neg, neg_neg, hσ1 x₀ x₁ h01]
  | cons p l ih =>
    obtain ⟨x₂, x₃⟩ := p
    -- the facts about the cycle
    simp only [pairVerts_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨h01, h02, h03, h0l⟩, ⟨h12, h13, h1l⟩, ⟨h23, h2l⟩, h3l, hl⟩ := hnd
    have hs : ∀ x, x = x₀ ∨ x = x₁ ∨ x = x₂ ∨ x = x₃ ∨ x ∈ pairVerts l → x ∈ s := by
      intro x hx
      apply hsub
      simp only [pairVerts_cons, List.mem_cons]
      tauto
    have hx₀ := hs x₀ (Or.inl rfl)
    have hx₁ := hs x₁ (Or.inr (Or.inl rfl))
    have hx₂ := hs x₂ (Or.inr (Or.inr (Or.inl rfl)))
    have hx₃ := hs x₃ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hm0 : m x₀ = x₁ := h1 _ (List.mem_cons_self ..)
    have hm2 : m x₂ = x₃ := h1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hml : ∀ q ∈ l, m q.1 = q.2 := fun q hq =>
      h1 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
    have hm1 : m x₁ = x₀ := by rw [← hm0, (hm x₀ hx₀).2.2]
    have hm3 : m x₃ = x₂ := by rw [← hm2, (hm x₂ hx₂).2.2]
    obtain ⟨hm'1, hm'3, hchain⟩ : m' x₁ = x₂ ∧ m' x₃ = nextFst x₀ l ∧ AltChain m' x₀ l := by
      simpa [AltChain, nextFst] using h2
    have hm'2 : m' x₂ = x₁ := by rw [← hm'1, (hm' x₁ hx₁).2.2]
    -- the shorter cycle
    set s' := (s.erase x₁).erase x₂ with hs'
    set μ : ι → ι := fun y => if y = x₀ then x₃ else if y = x₃ then x₀ else m y with hμ
    have hμ0 : μ x₀ = x₃ := by simp [μ]
    have hμ3 : μ x₃ = x₀ := by simp [μ, Ne.symm h03]
    have hμ : ∀ y, y ≠ x₀ → y ≠ x₃ → μ y = m y := fun y h0 h3 => by simp [μ, h0, h3]
    have hmem' : ∀ y, y ∈ s' ↔ y ∈ s ∧ y ≠ x₁ ∧ y ≠ x₂ := by
      intro y
      simp only [hs', mem_erase]
      tauto
    have hμm : IsMatchingOn s' μ := by
      intro y hy
      rw [hmem'] at hy
      obtain ⟨hys, hy1, hy2⟩ := hy
      by_cases e0 : y = x₀
      · subst e0
        rw [hμ0, hμ3, hmem']
        exact ⟨⟨hx₃, Ne.symm h13, Ne.symm h23⟩, Ne.symm h03, rfl⟩
      by_cases e3 : y = x₃
      · subst e3
        rw [hμ3, hμ0, hmem']
        exact ⟨⟨hx₀, h01, h02⟩, h03, rfl⟩
      obtain ⟨a1, a2, a3⟩ := hm y hys
      have n0 : m y ≠ x₀ := fun h => hy1 (by rw [← a3, h, hm0])
      have n1 : m y ≠ x₁ := fun h => e0 (by rw [← a3, h, hm1])
      have n2 : m y ≠ x₂ := fun h => e3 (by rw [← a3, h, hm2])
      have n3 : m y ≠ x₃ := fun h => hy2 (by rw [← a3, h, hm3])
      rw [hμ y e0 e3, hmem', hμ _ n0 n3]
      exact ⟨⟨a1, n1, n2⟩, a2, a3⟩
    have hm'm : IsMatchingOn s' m' := by
      intro y hy
      rw [hmem'] at hy
      obtain ⟨hys, hy1, hy2⟩ := hy
      obtain ⟨a1, a2, a3⟩ := hm' y hys
      refine ⟨(hmem' _).2 ⟨a1, fun h => hy2 ?_, fun h => hy1 ?_⟩, a2, a3⟩
      · rw [← a3, h, hm'1]
      · rw [← a3, h, hm'2]
    have IH := ih (s := s') (m := μ) x₃ hμm hm'm
      (by
        simp only [pairVerts_cons, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨h03, h0l⟩, h3l, hl⟩)
      (by
        intro x hx
        simp only [pairVerts_cons, List.mem_cons] at hx
        rw [hmem']
        rcases hx with rfl | rfl | hx
        · exact ⟨hx₀, h01, h02⟩
        · exact ⟨hx₃, Ne.symm h13, Ne.symm h23⟩
        · exact ⟨hs x (by tauto), fun h => h1l (h ▸ hx), fun h => h2l (h ▸ hx)⟩)
      (by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hμ0
        · have hq1 : q.1 ∈ pairVerts l := by
            simp only [pairVerts, List.mem_flatMap]
            exact ⟨q, hq, by simp⟩
          rw [hμ _ (fun h => h0l (h ▸ hq1)) (fun h => h3l (h ▸ hq1)), hml q hq])
      ⟨hm'3, hchain⟩
      (by
        intro x hx hxl
        rw [hmem'] at hx
        simp only [pairVerts_cons, List.mem_cons, not_or] at hxl
        rw [hμ x hxl.1 hxl.2.1]
        exact hagree x hx.1 (by
          simp only [pairVerts_cons, List.mem_cons, not_or]
          exact ⟨hxl.1, hx.2.1, hx.2.2, hxl.2.1, hxl.2.2⟩))
    -- expansions
    have hx₀' : x₀ ∈ s.erase x₁ := mem_erase.2 ⟨h01, hx₀⟩
    have hx₂' : x₂ ∈ s.erase x₁ := mem_erase.2 ⟨Ne.symm h12, hx₂⟩
    have E1 := pfOn_matchingMatrix_expand hσ hm hx₁
    rw [hm1] at E1
    have hm₁ := hm.erase_erase hx₁
    rw [hm1] at hm₁
    have hx₂₁ : x₂ ∈ (s.erase x₁).erase x₀ := mem_erase.2 ⟨Ne.symm h02, hx₂'⟩
    have E2 := pfOn_matchingMatrix_expand hσ hm₁ hx₂₁
    rw [hm2] at E2
    have hx₀s' : x₀ ∈ s' := (hmem' x₀).2 ⟨hx₀, h01, h02⟩
    have E3 := pfOn_matchingMatrix_expand hσ hμm hx₀s'
    rw [hμ0] at E3
    have E5 := pfOn_matchingMatrix_expand hσ hm' hx₁
    rw [hm'1] at E5
    have E4 : pfOn (matchingMatrix σ ((s'.erase x₀).erase x₃) μ) ((s'.erase x₀).erase x₃) =
        pfOn (matchingMatrix σ ((((s.erase x₁).erase x₀).erase x₂).erase x₃) m)
          ((((s.erase x₁).erase x₀).erase x₂).erase x₃) := by
      have hset : (s'.erase x₀).erase x₃ = (((s.erase x₁).erase x₀).erase x₂).erase x₃ := by
        ext y
        simp only [hs', mem_erase]
        tauto
      rw [hset]
      refine pfOn_congr fun i hi j _ => ?_
      have hi' := hi
      simp only [mem_erase] at hi'
      simp only [matchingMatrix, hi, true_and, hμ i hi'.2.2.1 hi'.1]
    have hsign := pairSign_flip (R := R) (x₃ := x₃) hx₁ hx₀' hx₂' h02
    have hs01 := hσ x₀ x₁ h01
    have hc := pairSign_mul_self (R := R) s' x₀ x₃
    have hsq := hσ1 x₀ x₃ h03
    rw [E1, E2, E5]
    rw [E3, E4] at IH
    simp only [altProd, nextFst_cons] at IH ⊢
    set A := pairSign (R := R) s x₁ x₀
    set B := pairSign (R := R) ((s.erase x₁).erase x₀) x₂ x₃
    set C := pairSign (R := R) s' x₀ x₃
    set D := pairSign (R := R) s x₁ x₂
    set Q := pfOn (matchingMatrix σ ((((s.erase x₁).erase x₀).erase x₂).erase x₃) m)
      ((((s.erase x₁).erase x₀).erase x₂).erase x₃)
    set Y := pfOn (matchingMatrix σ s' m') s'
    set T := σ x₃ (nextFst x₀ l) * altProd σ x₀ l
    set S := σ x₀ x₁ * σ x₁ x₂ * σ x₂ x₃
    linear_combination (A * B * σ x₂ x₃ * Q * D * σ x₁ x₂ * Y) * hs01 +
      (A * B * D * S * Q * Y) * hc + (-C * S * Q * Y) * hsign + (S * σ x₀ x₃) * IH +
      (-(S * T + C * S * Q * Y)) * hsq

end Kasteleyn
