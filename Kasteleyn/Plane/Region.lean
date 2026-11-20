module

public import Kasteleyn.Plane.Cochain
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Euler's inequality for a region of a rotation system

A *region* of a rotation system is a set `R` of faces. Its vertices and edges are the vertices
and edges incident with a face of `R`. We prove that if `R` is not the set of all faces and its
vertices are connected through its edges, then
`#vertices(R) - #edges(R) + #R ≤ 1`.

This is a dimension count over `ℚ`. Consider the linear map sending a function `p` on the
vertices of `R` and a function `σ` on `R` (extended by zero to all faces) to the function on the
edges of `R` given by `p (head) - p (tail) + σ (left face) - σ (right face)`. The two parts are
orthogonal (summing around the boundary walk of each face of `R` telescopes), so the kernel
consists of the pairs with both parts zero: `p` is constant by connectedness, and `σ` vanishes
because a function on faces which agrees on the two sides of every edge is constant, and `σ` is
zero outside `R`.

Applied to the two sides of a cycle of a plane graph, together with Euler's formula, this gives
Euler's formula for the disc bounded by the cycle (see `Kasteleyn.Plane.Cycle`).
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph Module

variable {V : Type*} {G : SimpleGraph V}

/-- Extension by zero of a function on a finite set. -/
def extendZero {α : Type*} [DecidableEq α] (s : Finset α) : (s → ℚ) →ₗ[ℚ] (α → ℚ) where
  toFun p a := if h : a ∈ s then p ⟨a, h⟩ else 0
  map_add' p q := by
    funext a
    by_cases h : a ∈ s <;> simp [h]
  map_smul' r p := by
    funext a
    by_cases h : a ∈ s <;> simp [h]

lemma extendZero_of_mem {α : Type*} [DecidableEq α] {s : Finset α} (p : s → ℚ) {a : α}
    (h : a ∈ s) : extendZero s p a = p ⟨a, h⟩ := by
  simp [extendZero, h]

lemma extendZero_of_notMem {α : Type*} [DecidableEq α] {s : Finset α} (p : s → ℚ) {a : α}
    (h : a ∉ s) : extendZero s p a = 0 := by
  simp [extendZero, h]

namespace RotationSystem

variable (M : RotationSystem G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The vertices of a region: the vertices incident with one of its faces. -/
def regionVerts (R : Finset M.Face) : Finset V := {v | ∃ d : G.Dart, d.fst = v ∧ M.face d ∈ R}

/-- The edges of a region: the edges incident with one of its faces. -/
def regionEdges (R : Finset M.Face) : Finset G.edgeSet :=
  {e | ∃ d : G.Dart, dartEdge d = e ∧ M.face d ∈ R}

variable {M}

lemma mem_regionVerts {R : Finset M.Face} {v : V} :
    v ∈ M.regionVerts R ↔ ∃ d : G.Dart, d.fst = v ∧ M.face d ∈ R := by
  simp [regionVerts]

lemma dartEdge_mem_regionEdges {R : Finset M.Face} {d : G.Dart} :
    dartEdge d ∈ M.regionEdges R ↔ M.face d ∈ R ∨ M.face d.symm ∈ R := by
  simp only [regionEdges, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨d', hd', hR⟩
    rcases dartEdge_eq_iff.1 hd' with rfl | rfl
    · exact Or.inl hR
    · exact Or.inr hR
  · rintro (h | h)
    · exact ⟨d, rfl, h⟩
    · exact ⟨d.symm, dartEdge_symm d, h⟩

lemma fst_mem_regionVerts {R : Finset M.Face} {d : G.Dart} (h : dartEdge d ∈ M.regionEdges R) :
    d.fst ∈ M.regionVerts R := by
  rcases dartEdge_mem_regionEdges.1 h with h | h
  · exact mem_regionVerts.2 ⟨d, rfl, h⟩
  · refine mem_regionVerts.2 ⟨M.faceNext d.symm, ?_, by rwa [face_faceNext]⟩
    simp [M.fst_rot]

lemma snd_mem_regionVerts {R : Finset M.Face} {d : G.Dart} (h : dartEdge d ∈ M.regionEdges R) :
    d.snd ∈ M.regionVerts R := by
  have := fst_mem_regionVerts (d := d.symm) (by rwa [dartEdge_symm])
  simpa using this

omit [DecidableEq V] in
/-- The sum over all darts of `(p (head) - p (tail)) * σ (face)` vanishes: around the boundary
walk of each face the differences telescope. -/
lemma sum_darts_telescope (p : V → ℚ) (σ : M.Face → ℚ) :
    ∑ d : G.Dart, (p d.snd - p d.fst) * σ (M.face d) = 0 := by
  simp only [sub_mul, sum_sub_distrib]
  rw [sub_eq_zero]
  conv_rhs => rw [← Equiv.sum_comp M.faceNext]
  simp only [fst_faceNext, face_faceNext]

/-- **Euler's inequality for a region.** Let `R` be a set of faces, not containing every face,
whose vertices are all connected (to `v₀`) through edges of `R`. Then
`#vertices(R) + #R ≤ #edges(R) + 1`. -/
theorem card_regionVerts_add_card_le (hG : G.Connected) (R : Finset M.Face) {f₁ : M.Face}
    (hf₁ : f₁ ∉ R) {v₀ : V} (hv₀ : v₀ ∈ M.regionVerts R)
    (hconn : ∀ v ∈ M.regionVerts R, Relation.ReflTransGen
      (fun a b => ∃ d : G.Dart, d.fst = a ∧ d.snd = b ∧ dartEdge d ∈ M.regionEdges R) v v₀) :
    #(M.regionVerts R) + #R ≤ #(M.regionEdges R) + 1 := by
  classical
  choose rep hrep using (dartEdge_surjective : Function.Surjective (dartEdge : G.Dart → G.edgeSet))
  set VR := M.regionVerts R
  set ER := M.regionEdges R
  -- the values on an edge, through its chosen dart
  let a : (VR → ℚ) → G.edgeSet → ℚ := fun p e =>
    extendZero VR p (rep e).snd - extendZero VR p (rep e).fst
  let b : (R → ℚ) → G.edgeSet → ℚ := fun σ e =>
    extendZero R σ (M.face (rep e)) - extendZero R σ (M.face (rep e).symm)
  let Φ : ((VR → ℚ) × (R → ℚ)) →ₗ[ℚ] (ER → ℚ) :=
    { toFun := fun x e => a x.1 e + b x.2 e
      map_add' := fun x y => by
        funext e
        simp only [a, b, Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply]
        ring
      map_smul' := fun r x => by
        funext e
        simp only [a, b, Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  -- orthogonality of the two parts
  have horth : ∀ p σ, ∑ e : G.edgeSet, a p e * b σ e = 0 := by
    intro p σ
    set P := extendZero VR p
    set S := extendZero R σ
    have h1 : ∀ e : G.edgeSet, a p e * b σ e = ∑ d with dartEdge d = e,
        (P d.snd - P d.fst) * S (M.face d) := by
      intro e
      conv_rhs => rw [← hrep e]
      rw [filter_dartEdge_eq, sum_pair (Dart.symm_ne _).symm]
      simp only [a, b, Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
      ring
    rw [sum_congr rfl fun e _ => h1 e, sum_fiberwise]
    exact M.sum_darts_telescope P S
  -- `b` vanishes outside the edges of the region
  have hb0 : ∀ σ e, e ∉ ER → b σ e = 0 := by
    intro σ e he
    have h' := mt (dartEdge_mem_regionEdges (R := R) (d := rep e)).2
    rw [hrep] at h'
    push Not at h'
    obtain ⟨h1, h2⟩ := h' he
    simp [b, extendZero_of_notMem _ h1, extendZero_of_notMem _ h2]
  -- the kernel is spanned by the constant function on the vertices
  have hker : LinearMap.ker Φ ≤ Submodule.span ℚ {((fun _ => 1 : VR → ℚ), (0 : R → ℚ))} := by
    rintro ⟨p, σ⟩ hx
    have hx' : ∀ e ∈ ER, a p e + b σ e = 0 := fun e he =>
      congrFun (LinearMap.mem_ker.1 hx) ⟨e, he⟩
    have hsq : ∑ e ∈ ER, a p e ^ 2 = 0 := by
      have h1 := horth p σ
      rw [← sum_subset (subset_univ ER) fun e _ he => by rw [hb0 σ e he, mul_zero]] at h1
      calc ∑ e ∈ ER, a p e ^ 2
          = ∑ e ∈ ER, (a p e * (a p e + b σ e) - a p e * b σ e) :=
            sum_congr rfl fun e _ => by ring
        _ = 0 := by
          rw [sum_sub_distrib, h1, sub_zero]
          exact sum_eq_zero fun e he => by rw [hx' e he, mul_zero]
    have ha : ∀ e ∈ ER, a p e = 0 := fun e he =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hsq e he)
    have hb : ∀ e, b σ e = 0 := by
      intro e
      by_cases he : e ∈ ER
      · have := hx' e he
        rwa [ha e he, zero_add] at this
      · exact hb0 σ e he
    -- `σ` vanishes
    have hS : ∀ d : G.Dart, extendZero R σ (M.face d.symm) = extendZero R σ (M.face d) := by
      intro d
      have h := hb (dartEdge d)
      simp only [b] at h
      rcases dartEdge_eq_iff.1 (hrep (dartEdge d)) with h' | h'
      · rw [h'] at h
        linarith
      · rw [h', Dart.symm_symm] at h
        linarith
    have hσ : σ = 0 := by
      funext f
      have := M.face_const hG hS f.1 f₁
      rw [extendZero_of_mem _ f.2, extendZero_of_notMem _ hf₁] at this
      exact this
    -- `p` is constant
    have hP : ∀ d : G.Dart, dartEdge d ∈ ER →
        extendZero VR p d.fst = extendZero VR p d.snd := by
      intro d hd
      have h := ha _ hd
      simp only [a] at h
      rcases dartEdge_eq_iff.1 (hrep (dartEdge d)) with h' | h'
      · rw [h'] at h
        linarith
      · rw [h'] at h
        simp only [Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap] at h
        linarith
    have hp : ∀ v ∈ VR, extendZero VR p v = extendZero VR p v₀ := by
      intro v hv
      induction hconn v hv using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab _ ih =>
        obtain ⟨d, rfl, rfl, hd⟩ := hab
        rw [hP d hd, ih (snd_mem_regionVerts hd)]
    rw [Submodule.mem_span_singleton]
    refine ⟨p ⟨v₀, hv₀⟩, ?_⟩
    rw [hσ]
    ext v
    · have := hp v.1 v.2
      rw [extendZero_of_mem _ v.2, extendZero_of_mem _ hv₀] at this
      simp [this]
    · simp
  -- the dimension count
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at h1
  have h2 := Submodule.finrank_le (LinearMap.range Φ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  have h3 := (Submodule.finrank_mono hker).trans (finrank_span_le_card _)
  rw [Set.toFinset_singleton, card_singleton] at h3
  omega

end RotationSystem

end Kasteleyn
