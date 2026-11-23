module

public import Kasteleyn.Spec
public import Kasteleyn.Plane.Matching
public import Kasteleyn.Machine.OrientBridge
public import WordRAM.Machine.IsWord

/-!
# The five targets of `Kasteleyn/Spec.lean`

The targets are stated in `Kasteleyn/Spec.lean`; this file proves them from the library.

* `Kasteleyn.orientation_exists` (`OrientationExists`): from
  `Kasteleyn.RotationSystem.exists_isKasteleyn`, with an auxiliary linear order on the vertices
  (the construction orients edges from smaller to larger vertices before reversing the edges of
  paths in a spanning tree of the dual graph).
* `Kasteleyn.pfaffian_formula` (`PfaffianFormula`): `Kasteleyn.pf_signedAdj_eq`.
* `Kasteleyn.matching_count` (`MatchingCount`): `Kasteleyn.pf_signedAdj_one_eq` and
  `Kasteleyn.det_signedAdj_eq`.
* `Kasteleyn.linear_time_orientation` (`LinearTimeOrientation`): the program
  `compile Orient.orient 0 ++ [halt]` and `Kasteleyn.Orient.orient_rotationSystem`.
* `Kasteleyn.edgeless_case` (`EdgelessCase`): a connected graph without edges has one vertex, no
  darts and no perfect matching, and its signed adjacency matrix is zero.
-/

@[expose] public section

namespace Kasteleyn

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt

universe u v

/-- **Existence of Kasteleyn orientations.** -/
theorem orientation_exists : OrientationExists.{u} := by
  intro V _ inst G _ M hG _ f₀
  exact @RotationSystem.exists_isKasteleyn V G M _ inst _
    (LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective) hG f₀

/-- **Kasteleyn's theorem**, weighted form. -/
theorem pfaffian_formula : PfaffianFormula.{u, v} := by
  intro V _ _ G _ M hM o f₀ ho R _ w
  exact pf_signedAdj_eq hM ho w

/-- **Kasteleyn's theorem**, counting form. -/
theorem matching_count : MatchingCount.{u} := by
  intro V _ _ G _ M hM o f₀ ho
  obtain ⟨ε, hε, h⟩ := pf_signedAdj_one_eq (R := ℤ) hM ho
  refine ⟨?_, det_signedAdj_eq hM ho⟩
  rcases hε with rfl | rfl
  · left; rw [h, one_mul]
  · right; rw [h, neg_one_mul]

/-- **A Kasteleyn orientation in linear time.** -/
theorem linear_time_orientation : LinearTimeOrientation.{u} := by
  refine ⟨compile Orient.orient 0 ++ [Instr.halt],
    Stmt.isWord_compile_halt (by kernel_rfl), ?_⟩
  intro V _ _ G _ M eF eD hG _ f₀
  obtain ⟨hlen, o, hK, hR⟩ := Orient.orient_rotationSystem (M := M) (eF := eF) (eD := eD) hG f₀
  refine ⟨hlen, _, hR, by simp, ?_⟩
  have key : ∀ x : G.Dart, ((List.range (Fintype.card G.Dart)).map o).getD
      (Orient.pos M eF eD x) 0 = o (Orient.pos M eF eD x) := by
    intro x
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Orient.pos_lt x)]
    rfl
  simpa only [key] using hK

/-- **The graph without edges.** -/
theorem edgeless_case : EdgelessCase.{u, v} := by
  intro V _ _ G _ hG hE
  have hadj : ∀ x y, ¬ G.Adj x y := by
    intro x y h
    have hm : s(x, y) ∈ G.edgeFinset := by simpa using h
    simp [hE] at hm
  have hsub : ∀ x y : V, x = y := by
    intro x y
    obtain ⟨p⟩ := hG.preconnected x y
    cases p with
    | nil => rfl
    | cons h _ => exact absurd h (hadj _ _)
  obtain ⟨x₀⟩ := hG.nonempty
  have hcard : Fintype.card V = 1 :=
    Fintype.card_eq_one_iff.2 ⟨x₀, fun y => hsub y x₀⟩
  have hPM : graphPerfectMatchings G = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.2 fun μ hμ => ?_
    simp only [graphPerfectMatchings, perfectMatchingsOn, Finset.mem_filter, Finset.mem_univ,
      true_and] at hμ
    exact (hμ.1.2 x₀).1 (hsub _ _) (Finset.mem_univ x₀)
  refine ⟨hcard, ⟨fun d => hadj _ _ d.adj⟩, hPM, fun o R _ w => ⟨?_, ?_⟩⟩
  · rw [hPM, Finset.sum_empty]
    simp [pf, pfOn, Finset.card_univ, hcard, pfAux]
  · rw [hPM, Finset.card_empty]
    have h0 : signedAdj o (fun _ => (1 : ℤ)) = 0 := by
      ext x y
      simp [signedAdj, hadj x y]
    have : Nonempty V := ⟨x₀⟩
    rw [h0, Matrix.det_zero]
    simp

end Kasteleyn

end
