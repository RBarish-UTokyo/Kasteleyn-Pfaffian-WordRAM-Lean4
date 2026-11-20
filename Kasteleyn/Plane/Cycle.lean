module

public import Kasteleyn.Plane.Orientation
public import Kasteleyn.Plane.Region

/-!
# Cycles of a plane graph and Kasteleyn's cycle lemma

A cycle of a simple graph `G` is described by its finite set of vertices `verts` together with a
successor function `next`, which permutes `verts` cyclically along edges of `G`
(`Kasteleyn.GraphCycle`). Its *forward darts* are the darts `v → next v`.

## The inside of a cycle

Let `M` be a plane rotation system on `G` and `f₀` a face (the outer face). The edges of a cycle
`C` form a set of edges of even degree at every vertex, so by
`Kasteleyn.RotationSystem.exists_face_cochain` there is a set `I` of faces such that an edge
separates a face of `I` from a face outside `I` exactly when it is an edge of `C`
(`Kasteleyn.RotationSystem.Separates`); replacing `I` by its complement we may assume `f₀ ∉ I`.
This is the combinatorial Jordan curve theorem: `I` is the set of faces *inside* `C`. The
*vertices strictly inside* `C` are the vertices of `I` which are not on `C`.

Both `I` and its complement are regions whose vertices are connected through their edges, so
Euler's inequality for regions (`Kasteleyn.RotationSystem.card_regionVerts_add_card_le`) applies
to each; since the two inequalities add up to Euler's formula for `M`, both are equalities. This
gives Euler's formula `V - E + F = 1` for the disc bounded by `C`.

## Main results

* `Kasteleyn.RotationSystem.exists_inside`: every cycle has an inside.
* `Kasteleyn.RotationSystem.Separates.face_fwd_iff`: the forward darts of a cycle all have their
  face inside, or all outside: the cycle is traversed with its inside consistently on one side.
* `Kasteleyn.RotationSystem.odd_card_cw_add_card_inner`: **Kasteleyn's cycle lemma**: for a
  Kasteleyn orientation, the number of edges of a cycle which are clockwise with respect to its
  inside, plus the number of vertices strictly inside, is odd.
* `Kasteleyn.RotationSystem.odd_card_fwd_add_card_inner`: the same for the number of forward
  darts which are oriented forward, for a cycle of even length.

## References

* P. W. Kasteleyn, *Dimer statistics and phase transitions*, J. Math. Phys. 4 (1963), 287–293.
* P. W. Kasteleyn, *Graph theory and crystal physics*, in *Graph Theory and Theoretical Physics*,
  Academic Press (1967), 43–110.
* L. Lovász, M. D. Plummer, *Matching Theory*, North-Holland (1986), §8.3.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A cycle of `G`: a finite nonempty set of vertices `verts` with a successor function `next`
which permutes `verts` in a single cycle along edges of `G`, and has no cycles of length `2`
(so the cycle has length at least `3`). -/
structure GraphCycle (G : SimpleGraph V) where
  /-- The vertices of the cycle. -/
  verts : Finset V
  /-- The successor of a vertex along the cycle. -/
  next : V → V
  next_mem : ∀ v ∈ verts, next v ∈ verts
  adj_next : ∀ v ∈ verts, G.Adj v (next v)
  next_injOn : ∀ u ∈ verts, ∀ v ∈ verts, next u = next v → u = v
  next_next_ne : ∀ v ∈ verts, next (next v) ≠ v
  reach : ∀ u ∈ verts, ∀ v ∈ verts, ∃ n : ℕ, next^[n] u = v
  nonempty : verts.Nonempty

namespace GraphCycle

variable (C : GraphCycle G)

lemma iterate_mem (n : ℕ) {v : V} (hv : v ∈ C.verts) : C.next^[n] v ∈ C.verts := by
  induction n generalizing v with
  | zero => exact hv
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (C.next_mem v hv)

lemma exists_prev {v : V} (hv : v ∈ C.verts) : ∃ u ∈ C.verts, C.next u = v := by
  obtain ⟨n, hn⟩ := C.reach _ (C.next_mem v hv) v hv
  cases n with
  | zero =>
    exfalso
    have h : C.next v = v := hn
    exact C.next_next_ne v hv (by rw [h, h])
  | succ n =>
    exact ⟨_, C.iterate_mem n (C.next_mem v hv),
      (Function.iterate_succ_apply' C.next n (C.next v)).symm.trans hn⟩

/-- A forward dart of the cycle: `v → next v` with `v` on the cycle. -/
def IsFwd (d : G.Dart) : Prop := d.fst ∈ C.verts ∧ d.snd = C.next d.fst

/-- A dart of an edge of the cycle (in either direction). -/
def OnCycle (d : G.Dart) : Prop := C.IsFwd d ∨ C.IsFwd d.symm

instance [DecidableEq V] : DecidablePred C.IsFwd := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq V] : DecidablePred C.OnCycle := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

lemma onCycle_symm (d : G.Dart) : C.OnCycle d.symm ↔ C.OnCycle d := by
  simp only [OnCycle, Dart.symm_symm, or_comm]

/-- The forward dart leaving a vertex of the cycle. -/
def outDart (v : V) (hv : v ∈ C.verts) : G.Dart := ⟨(v, C.next v), C.adj_next v hv⟩

@[simp] lemma outDart_fst (v : V) (hv : v ∈ C.verts) : (C.outDart v hv).fst = v := rfl

@[simp] lemma outDart_snd (v : V) (hv : v ∈ C.verts) : (C.outDart v hv).snd = C.next v := rfl

lemma isFwd_outDart (v : V) (hv : v ∈ C.verts) : C.IsFwd (C.outDart v hv) := ⟨hv, rfl⟩

lemma onCycle_outDart (v : V) (hv : v ∈ C.verts) : C.OnCycle (C.outDart v hv) :=
  Or.inl (C.isFwd_outDart v hv)

lemma eq_outDart {d : G.Dart} (hd : C.IsFwd d) : d = C.outDart d.fst hd.1 :=
  Dart.ext _ _ (Prod.ext rfl hd.2)

lemma fst_mem_of_onCycle {d : G.Dart} (hd : C.OnCycle d) : d.fst ∈ C.verts := by
  rcases hd with hd | hd
  · exact hd.1
  · have h := hd.2
    simp only [Dart.symm_toProd, Prod.snd_swap, Prod.fst_swap] at h
    rw [h]
    exact C.next_mem _ hd.1

/-- The darts of the cycle leaving `v` are the darts to `next v` and to the predecessor `u`. -/
lemma onCycle_iff {u v : V} (hu : u ∈ C.verts) (huv : C.next u = v) {d : G.Dart}
    (hd : d.fst = v) : C.OnCycle d ↔ d.snd = C.next v ∨ d.snd = u := by
  have hv : v ∈ C.verts := huv ▸ C.next_mem u hu
  constructor
  · rintro (h | h)
    · exact Or.inl (hd ▸ h.2)
    · right
      obtain ⟨h1, h2⟩ := h
      simp only [Dart.symm_toProd, Prod.snd_swap, Prod.fst_swap] at h1 h2
      exact C.next_injOn _ h1 _ hu (by rw [← h2, hd, huv])
  · rintro (h | h)
    · exact Or.inl ⟨hd ▸ hv, hd ▸ h⟩
    · right
      refine ⟨?_, ?_⟩ <;> simp only [Dart.symm_toProd, Prod.snd_swap, Prod.fst_swap]
      · rw [h]; exact hu
      · rw [h, huv, hd]

lemma next_ne_prev {u v : V} (hu : u ∈ C.verts) (huv : C.next u = v) : C.next v ≠ u := by
  intro h
  exact C.next_next_ne u hu (by rw [huv, h])

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The edges of the cycle. -/
def edges : Finset G.edgeSet := {e | ∃ d, dartEdge d = e ∧ C.IsFwd d}

lemma dartEdge_mem_edges {d : G.Dart} : dartEdge d ∈ C.edges ↔ C.OnCycle d := by
  simp only [edges, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨d', hd', hf⟩
    rcases dartEdge_eq_iff.1 hd' with rfl | rfl
    · exact Or.inl hf
    · exact Or.inr hf
  · rintro (h | h)
    · exact ⟨d, rfl, h⟩
    · exact ⟨d.symm, dartEdge_symm d, h⟩

/-- A cycle has as many forward darts as vertices. -/
lemma card_isFwd : #({d | C.IsFwd d} : Finset G.Dart) = #C.verts := by
  refine card_bij (fun d _ => d.fst) (fun d hd => (mem_filter.1 hd).2.1)
    (fun d hd d' hd' h => ?_) (fun v hv => ⟨C.outDart v hv, by simp [C.isFwd_outDart], rfl⟩)
  rw [C.eq_outDart (mem_filter.1 hd).2, C.eq_outDart (mem_filter.1 hd').2]
  exact Dart.ext _ _ (Prod.ext h (by simp [h]))

/-- A cycle has as many edges as vertices. -/
lemma card_edges : #C.edges = #C.verts := by
  symm
  refine card_bij (fun v hv => dartEdge (C.outDart v hv)) (fun v hv => ?_) ?_ ?_
  · exact C.dartEdge_mem_edges.2 (C.onCycle_outDart v hv)
  · intro v hv w hw h
    rcases dartEdge_eq_iff.1 h with h | h
    · exact congrArg (fun d : G.Dart => d.fst) h
    · have h1 : v = C.next w := congrArg (fun d : G.Dart => d.fst) h
      have h2 : C.next v = w := congrArg (fun d : G.Dart => d.snd) h
      exact absurd (by rw [← h1]; exact h2) (C.next_next_ne w hw)
  · intro e he
    obtain ⟨d, rfl, hd⟩ := by simpa [edges] using he
    exact ⟨d.fst, hd.1, by rw [← C.eq_outDart hd]⟩

/-- The set of edges of a cycle, as a cochain modulo `2`. -/
def cochain : G.edgeSet → ZMod 2 := fun e => if e ∈ C.edges then 1 else 0

/-- Every vertex has even degree in a cycle. -/
lemma sum_cochain (v : V) : ∑ d with d.fst = v, C.cochain (dartEdge d) = 0 := by
  simp only [cochain, C.dartEdge_mem_edges]
  rw [← sum_filter, filter_filter]
  by_cases hv : v ∈ C.verts
  · obtain ⟨u, hu, huv⟩ := C.exists_prev hv
    have hne : C.next v ≠ u := C.next_ne_prev hu huv
    have : ({d | d.fst = v ∧ C.OnCycle d} : Finset G.Dart) =
        {C.outDart v hv, ⟨(v, u), (G.adj_symm (huv ▸ C.adj_next u hu))⟩} := by
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hd, h⟩
        rcases (C.onCycle_iff hu huv hd).1 h with h | h
        · exact Or.inl (Dart.ext _ _ (Prod.ext hd h))
        · exact Or.inr (Dart.ext _ _ (Prod.ext hd h))
      · rintro (rfl | rfl)
        · exact ⟨rfl, C.onCycle_outDart v hv⟩
        · exact ⟨rfl, (C.onCycle_iff hu huv rfl).2 (Or.inr rfl)⟩
    rw [this, sum_pair]
    · rfl
    · intro h
      exact hne (congrArg (fun d : G.Dart => d.snd) h)
  · rw [sum_eq_zero]
    intro d hd
    exact absurd ((mem_filter.1 hd).2.1 ▸ C.fst_mem_of_onCycle (mem_filter.1 hd).2.2) hv

end GraphCycle

namespace RotationSystem

variable (M : RotationSystem G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A set `R` of faces is *separated* by the cycle `C` if the edges of `C` are exactly the edges
with a face of `R` on one side and a face outside `R` on the other side. -/
def Separates (C : GraphCycle G) (R : Finset M.Face) : Prop :=
  ∀ d : G.Dart, (M.face d.symm ∈ R ↔ M.face d ∈ R) ↔ ¬ C.OnCycle d

variable {M} {C : GraphCycle G} {R : Finset M.Face}

/-- **The inside of a cycle.** For every cycle of a plane graph and every face `f₀` there is a
set of faces, not containing `f₀`, separated by the cycle: the faces inside the cycle. -/
theorem exists_inside (hM : M.IsPlane) (C : GraphCycle G) (f₀ : M.Face) :
    ∃ I : Finset M.Face, M.Separates C I ∧ f₀ ∉ I := by
  obtain ⟨h, hh⟩ := M.exists_face_cochain hM C.cochain C.sum_cochain
  refine ⟨univ.filter fun f => h f ≠ h f₀, fun d => ?_, by simp⟩
  have := hh d
  simp only [GraphCycle.cochain, C.dartEdge_mem_edges] at this
  simp only [mem_filter, mem_univ, true_and]
  generalize h (M.face d) = a, h (M.face d.symm) = b, h f₀ = c at this
  by_cases hC : C.OnCycle d <;> simp only [hC, ↓reduceIte, not_true, not_false_iff] at this ⊢
  · revert a b c
    decide
  · revert a b c
    decide

namespace Separates

variable (hR : M.Separates C R)
include hR

lemma compl : M.Separates C Rᶜ := by
  intro d
  rw [← hR d, mem_compl, mem_compl, not_iff_not]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma iff_of_not_onCycle {d : G.Dart} (hd : ¬ C.OnCycle d) :
    M.face d.symm ∈ R ↔ M.face d ∈ R :=
  (hR d).2 hd

lemma iff_of_onCycle {d : G.Dart} (hd : C.OnCycle d) :
    M.face d.symm ∈ R ↔ M.face d ∉ R := by
  have h := mt (hR d).1 (not_not.2 hd)
  tauto

omit [DecidableEq V] in
/-- Around a vertex off the cycle all faces are on the same side. -/
lemma iff_of_notMem {v : V} (hv : v ∉ C.verts) {d d' : G.Dart} (hd : d.fst = v)
    (hd' : d'.fst = v) : M.face d ∈ R ↔ M.face d' ∈ R := by
  obtain ⟨n, rfl⟩ := M.exists_rot_pow_eq (hd.trans hd'.symm)
  clear hd'
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : ¬ C.OnCycle ((M.rot ^ n) d) := fun h => hv (by
      have := C.fst_mem_of_onCycle h
      rwa [M.fst_rot_pow, hd] at this)
    rw [pow_succ', Equiv.Perm.mul_apply, face_rot, hR.iff_of_not_onCycle hx]
    exact ih

lemma mem_regionVerts {v : V} (hv : v ∈ C.verts) : v ∈ M.regionVerts R := by
  by_cases h : M.face (C.outDart v hv) ∈ R
  · exact RotationSystem.mem_regionVerts.2 ⟨_, rfl, h⟩
  · refine RotationSystem.mem_regionVerts.2 ⟨M.rot (C.outDart v hv), M.fst_rot _, ?_⟩
    rw [face_rot]
    exact (hR.iff_of_onCycle (C.onCycle_outDart v hv)).2 h

lemma dartEdge_mem_regionEdges {d : G.Dart} (hd : C.OnCycle d) :
    dartEdge d ∈ M.regionEdges R := by
  rw [RotationSystem.dartEdge_mem_regionEdges]
  have := hR.iff_of_onCycle hd
  tauto

/-- A vertex off the cycle with a face in `R` has all its neighbours in the vertices of `R`. -/
lemma snd_mem_regionVerts {d : G.Dart} (hd : d.fst ∉ C.verts)
    (hv : d.fst ∈ M.regionVerts R) : d.snd ∈ M.regionVerts R ∧ M.face d ∈ R := by
  obtain ⟨d', hd', hd'R⟩ := RotationSystem.mem_regionVerts.1 hv
  have h1 : M.face (M.rot d) ∈ R := (hR.iff_of_notMem hd (M.fst_rot d) hd').2 hd'R
  rw [face_rot] at h1
  refine ⟨RotationSystem.mem_regionVerts.2 ⟨d.symm, by simp, h1⟩,
    (hR.iff_of_notMem hd rfl hd').2 hd'R⟩

/-- The vertices of `R` are connected through the edges of `R`. -/
lemma reach {v₀ : V} (hv₀ : v₀ ∈ C.verts) (hG : G.Connected) {v : V}
    (hv : v ∈ M.regionVerts R) : Relation.ReflTransGen
      (fun a b => ∃ d : G.Dart, d.fst = a ∧ d.snd = b ∧ dartEdge d ∈ M.regionEdges R) v v₀ := by
  -- vertices of the cycle
  have hcyc : ∀ v ∈ C.verts, Relation.ReflTransGen
      (fun a b => ∃ d : G.Dart, d.fst = a ∧ d.snd = b ∧ dartEdge d ∈ M.regionEdges R) v v₀ := by
    intro v hv
    obtain ⟨n, hn⟩ := C.reach v hv v₀ hv₀
    subst hn
    induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact Relation.ReflTransGen.head ⟨C.outDart v hv, rfl, rfl,
        hR.dartEdge_mem_regionEdges (C.onCycle_outDart v hv)⟩
        (ih _ (C.next_mem v hv) (C.iterate_mem n (C.next_mem v hv)))
  have hwalk : Relation.ReflTransGen G.Adj v v₀ :=
    (reachable_iff_reflTransGen _ _).1 (hG.preconnected _ _)
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact hcyc _ hv₀
  | @head a c hac _ ih =>
    by_cases ha : a ∈ C.verts
    · exact hcyc a ha
    have h := hR.snd_mem_regionVerts (d := ⟨(a, c), hac⟩) ha hv
    refine Relation.ReflTransGen.head ⟨⟨(a, c), hac⟩, rfl, rfl, ?_⟩ (ih h.1)
    exact RotationSystem.dartEdge_mem_regionEdges.2 (Or.inl h.2)

/-- On a vertex `w = next v` of the cycle, the forward darts leaving `v` and `w` have their faces
on the same side. -/
lemma face_outDart_next_iff {v : V} (hv : v ∈ C.verts) :
    M.face (C.outDart (C.next v) (C.next_mem v hv)) ∈ R ↔ M.face (C.outDart v hv) ∈ R := by
  set w := C.next v
  have hw : w ∈ C.verts := C.next_mem v hv
  set a := (C.outDart v hv).symm with ha_def
  set b := C.outDart w hw with hb_def
  have hafst : a.fst = w := rfl
  have hasnd : a.snd = v := rfl
  have hab : a ≠ b := fun h => C.next_next_ne v hv (by
    have := congrArg (fun d : G.Dart => d.snd) h
    simp only [hasnd] at this
    exact this.symm)
  -- the only darts of the cycle at `w` are `a` and `b`
  have hcyc : ∀ x : G.Dart, x.fst = w → x ≠ a → x ≠ b → ¬ C.OnCycle x := by
    intro x hx hxa hxb hon
    rcases (C.onCycle_iff hv rfl hx).1 hon with h | h
    · exact hxb (Dart.ext _ _ (Prod.ext hx h))
    · exact hxa (Dart.ext _ _ (Prod.ext hx h))
  have hex : ∃ n : ℕ, 0 < n ∧ (M.rot ^ n) b = a := by
    obtain ⟨n, hn⟩ := M.exists_rot_pow_eq (show b.fst = a.fst from rfl)
    refine ⟨n, Nat.pos_of_ne_zero fun h0 => hab ?_, hn⟩
    rw [← hn, h0, pow_zero, Equiv.Perm.one_apply]
  classical
  set k := Nat.find hex
  have hk : 0 < k ∧ (M.rot ^ k) b = a := Nat.find_spec hex
  have hmin : ∀ m, 0 < m → m < k → (M.rot ^ m) b ≠ a := fun m hm hmk h =>
    Nat.find_min hex hmk ⟨hm, h⟩
  have key : ∀ m, 0 < m → m ≤ k → (M.face ((M.rot ^ m) b) ∈ R ↔ M.face b ∉ R) := by
    intro m hm hmk
    induction m with
    | zero => exact absurd hm (lt_irrefl 0)
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, face_rot]
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · simpa using hR.iff_of_onCycle (C.onCycle_outDart w hw)
      · have hxa : (M.rot ^ m) b ≠ a := hmin m hm' (by omega)
        have hxb : (M.rot ^ m) b ≠ b := by
          intro h
          refine hmin (k - m) (by omega) (by omega) ?_
          have e : (M.rot ^ k) b = (M.rot ^ (k - m)) ((M.rot ^ m) b) := by
            rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega : m ≤ k)]
          rw [h] at e
          rw [← e, hk.2]
        rw [hR.iff_of_not_onCycle (hcyc _ (M.fst_rot_pow m b) hxa hxb)]
        exact ih hm' (by omega)
  have h1 := key k hk.1 le_rfl
  rw [hk.2] at h1
  have h2 := hR.iff_of_onCycle (show C.OnCycle a from (C.onCycle_symm _).2
    (C.onCycle_outDart v hv))
  rw [ha_def, Dart.symm_symm] at h2
  rw [h2]
  tauto

/-- **Consistency of the sides along a cycle.** The forward darts of the cycle have their faces
all in `R` or all outside `R`. -/
lemma face_outDart_iterate_iff {v : V} (hv : v ∈ C.verts) (n : ℕ) :
    M.face (C.outDart (C.next^[n] v) (C.iterate_mem n hv)) ∈ R ↔
      M.face (C.outDart v hv) ∈ R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : C.outDart (C.next^[n + 1] v) (C.iterate_mem (n + 1) hv) =
        C.outDart (C.next (C.next^[n] v)) (C.next_mem _ (C.iterate_mem n hv)) :=
      Dart.ext _ _ (Prod.ext (Function.iterate_succ_apply' _ _ _)
        (by simp only [GraphCycle.outDart_snd, Function.iterate_succ_apply']))
    rw [e, hR.face_outDart_next_iff (C.iterate_mem n hv), ih]

lemma face_fwd_iff {d d' : G.Dart} (hd : C.IsFwd d) (hd' : C.IsFwd d') :
    M.face d ∈ R ↔ M.face d' ∈ R := by
  obtain ⟨n, hn⟩ := C.reach _ hd.1 _ hd'.1
  have e : d' = C.outDart (C.next^[n] d.fst) (C.iterate_mem n hd.1) :=
    (C.eq_outDart hd').trans (Dart.ext _ _ (Prod.ext hn.symm (by simp [hn])))
  rw [e, hR.face_outDart_iterate_iff hd.1 n, ← C.eq_outDart hd]

end Separates

/-- **Euler's formula for the inside of a cycle.** If `R` is separated by a cycle of a plane
graph and neither `R` nor its complement is empty, then the vertices, edges and faces of `R`
satisfy `V - E + F = 1`. -/
theorem card_regionVerts_add_card (hM : M.IsPlane) (hR : M.Separates C R) {f₁ : M.Face}
    (hf₁ : f₁ ∉ R) :
    #(M.regionVerts R) + #R = #(M.regionEdges R) + 1 := by
  have hG := hM.connected
  obtain ⟨v₀, hv₀⟩ := C.nonempty
  have hRc := hR.compl
  -- a face in `R`
  obtain ⟨f₂, hf₂⟩ : ∃ f, f ∉ Rᶜ := by
    by_cases h : M.face (C.outDart v₀ hv₀) ∈ R
    · exact ⟨_, by simpa using h⟩
    · exact ⟨M.face (C.outDart v₀ hv₀).symm,
        by simpa using (hR.iff_of_onCycle (C.onCycle_outDart v₀ hv₀)).2 h⟩
  have h1 := M.card_regionVerts_add_card_le hG R hf₁ (hR.mem_regionVerts hv₀)
    fun v hv => hR.reach hv₀ hG hv
  have h2 := M.card_regionVerts_add_card_le hG Rᶜ hf₂ (hRc.mem_regionVerts hv₀)
    fun v hv => hRc.reach hv₀ hG hv
  -- vertices
  have hVu : M.regionVerts R ∪ M.regionVerts Rᶜ = univ := by
    rw [eq_univ_iff_forall]
    intro v
    obtain ⟨d, hd⟩ := hM.exists_dart v
    by_cases h : M.face d ∈ R
    · exact mem_union_left _ (mem_regionVerts.2 ⟨d, hd, h⟩)
    · exact mem_union_right _ (mem_regionVerts.2 ⟨d, hd, by simpa using h⟩)
  have hVi : M.regionVerts R ∩ M.regionVerts Rᶜ = C.verts := by
    ext v
    refine ⟨fun h => ?_, fun h => mem_inter.2 ⟨hR.mem_regionVerts h, hRc.mem_regionVerts h⟩⟩
    obtain ⟨h1, h2⟩ := mem_inter.1 h
    obtain ⟨d, hd, hdR⟩ := mem_regionVerts.1 h1
    obtain ⟨d', hd', hd'R⟩ := mem_regionVerts.1 h2
    by_contra hv
    exact (mem_compl.1 hd'R) ((hR.iff_of_notMem hv hd hd').1 hdR)
  -- edges
  have hEu : M.regionEdges R ∪ M.regionEdges Rᶜ = univ := by
    rw [eq_univ_iff_forall]
    intro e
    obtain ⟨d, rfl⟩ := dartEdge_surjective e
    by_cases h : M.face d ∈ R
    · exact mem_union_left _ (dartEdge_mem_regionEdges.2 (Or.inl h))
    · exact mem_union_right _ (dartEdge_mem_regionEdges.2 (Or.inl (by simpa using h)))
  have hEi : M.regionEdges R ∩ M.regionEdges Rᶜ = C.edges := by
    ext e
    obtain ⟨d, rfl⟩ := dartEdge_surjective e
    rw [mem_inter, dartEdge_mem_regionEdges, dartEdge_mem_regionEdges, mem_compl, mem_compl,
      C.dartEdge_mem_edges]
    have := hR d
    by_cases h1 : M.face d ∈ R <;> by_cases h2 : M.face d.symm ∈ R <;>
      simp only [h1, h2, true_iff, iff_true, not_true, not_false_iff, or_true,
        or_false, and_true, and_false, iff_false, false_iff, not_not] at this ⊢ <;> tauto
  have hV := card_union_add_card_inter (M.regionVerts R) (M.regionVerts Rᶜ)
  rw [hVu, hVi, card_univ] at hV
  have hE := card_union_add_card_inter (M.regionEdges R) (M.regionEdges Rᶜ)
  rw [hEu, hEi, card_univ, C.card_edges, ← edgeFinset_card] at hE
  have hF := card_add_card_compl R
  have he := hM.euler
  omega

/-- **Kasteleyn's cycle lemma.** Let `o` be a Kasteleyn orientation of a plane graph with
respect to the outer face `f₀`, and let `I` be the inside of a cycle `C`. Then the number of edges
of `C` which are clockwise with respect to the inside (oriented as the dart of `C` whose face is
inside), plus the number of vertices strictly inside `C`, is odd. -/
theorem odd_card_cw_add_card_inner (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) (C : GraphCycle G) {I : Finset M.Face} (hI : M.Separates C I)
    (hf₀ : f₀ ∉ I) :
    Odd (#{d | M.face d ∈ I ∧ C.OnCycle d ∧ o d = true} + #(M.regionVerts I \ C.verts)) := by
  have hχ := card_regionVerts_add_card hM hI hf₀
  -- the clockwise darts of the faces inside
  set K : Finset G.Dart := {d | M.face d ∈ I ∧ o d = true}
  have hK : (#K : ZMod 2) = #I := by
    rw [card_eq_sum_card_fiberwise (f := M.face) (t := I) fun d hd => (mem_filter.1 hd).2.1,
      Nat.cast_sum, card_eq_sum_ones I, Nat.cast_sum]
    refine sum_congr rfl fun f hf => ?_
    have hodd := ho.2 f (fun h => hf₀ (h ▸ hf))
    rw [← ZMod.natCast_eq_one_iff_odd, cwCount] at hodd
    rw [Nat.cast_one, ← hodd, filter_filter]
    congr 2
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, h⟩, rfl⟩
      exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨⟨hf, h⟩, rfl⟩
  rw [ZMod.natCast_eq_natCast_iff'] at hK
  -- split according to the edges of the cycle
  have hsplit := card_filter_add_card_filter_not (s := K) (p := C.OnCycle)
  have h1 : K.filter C.OnCycle =
      ({d | M.face d ∈ I ∧ C.OnCycle d ∧ o d = true} : Finset G.Dart) := by
    ext d
    simp only [K, mem_filter, mem_univ, true_and]
    tauto
  have h2 : #(K.filter fun d => ¬ C.OnCycle d) = #(M.regionEdges I \ C.edges) := by
    refine card_bij (fun d _ => dartEdge d) (fun d hd => ?_) (fun d hd d' hd' h => ?_)
      (fun e he => ?_)
    · simp only [K, mem_filter, mem_univ, true_and] at hd
      rw [mem_sdiff, dartEdge_mem_regionEdges, C.dartEdge_mem_edges]
      exact ⟨Or.inl hd.1.1, hd.2⟩
    · simp only [K, mem_filter, mem_univ, true_and] at hd hd'
      rcases dartEdge_eq_iff.1 h with h | rfl
      · exact h
      · have := ho.1 d'
        rw [hd.1.2, hd'.1.2] at this
        exact absurd this (by decide)
    · obtain ⟨d, rfl⟩ := dartEdge_surjective e
      rw [mem_sdiff, dartEdge_mem_regionEdges, C.dartEdge_mem_edges] at he
      have hboth := hI.iff_of_not_onCycle he.2
      have hdI : M.face d ∈ I := by tauto
      have hdI' : M.face d.symm ∈ I := hboth.2 hdI
      cases hod : o d
      · refine ⟨d.symm, ?_, dartEdge_symm d⟩
        simp only [K, mem_filter, mem_univ, true_and]
        refine ⟨⟨hdI', by rw [ho.1 d, hod]; rfl⟩, ?_⟩
        rw [C.onCycle_symm]
        exact he.2
      · exact ⟨d, by simp [K, hdI, hod, he.2], rfl⟩
  have h3 : C.edges ⊆ M.regionEdges I := by
    intro e he
    obtain ⟨d, rfl⟩ := dartEdge_surjective e
    exact hI.dartEdge_mem_regionEdges (C.dartEdge_mem_edges.1 he)
  have h4 := card_sdiff_add_card_eq_card h3
  have h5 : C.verts ⊆ M.regionVerts I := fun v hv => hI.mem_regionVerts hv
  have h6 := card_sdiff_add_card_eq_card h5
  rw [h1] at hsplit
  rw [h2] at hsplit
  have h7 := C.card_edges
  rw [Nat.odd_iff]
  omega

/-- **Kasteleyn's cycle lemma for even cycles.** Let `o` be a Kasteleyn orientation of a plane
graph with respect to the outer face `f₀`, and let `I` be the inside of a cycle `C` of even
length. Then the number of forward darts of `C` which are oriented forward, plus the number of
vertices strictly inside `C`, is odd. -/
theorem odd_card_fwd_add_card_inner (hM : M.IsPlane) {o : G.Dart → Bool} {f₀ : M.Face}
    (ho : M.IsKasteleyn o f₀) (C : GraphCycle G) (hC : Even #C.verts) {I : Finset M.Face}
    (hI : M.Separates C I) (hf₀ : f₀ ∉ I) :
    Odd (#{d | C.IsFwd d ∧ o d = true} + #(M.regionVerts I \ C.verts)) := by
  have h := odd_card_cw_add_card_inner hM ho C hI hf₀
  obtain ⟨v₀, hv₀⟩ := C.nonempty
  have hfwd := C.card_isFwd
  by_cases hin : M.face (C.outDart v₀ hv₀) ∈ I
  · -- the forward darts have their faces inside
    have : ({d | M.face d ∈ I ∧ C.OnCycle d ∧ o d = true} : Finset G.Dart) =
        ({d | C.IsFwd d ∧ o d = true} : Finset G.Dart) := by
      ext d
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hdI, hon, hod⟩
        refine ⟨?_, hod⟩
        rcases hon with hon | hon
        · exact hon
        · have h1 := (hI.face_fwd_iff hon (C.isFwd_outDart v₀ hv₀)).2 hin
          exact absurd hdI ((hI.iff_of_onCycle (Or.inr hon)).1 h1)
      · rintro ⟨hfw, hod⟩
        exact ⟨(hI.face_fwd_iff hfw (C.isFwd_outDart v₀ hv₀)).2 hin, Or.inl hfw, hod⟩
    rwa [this] at h
  · -- the backward darts have their faces inside
    have hsymm : ({d | M.face d ∈ I ∧ C.OnCycle d ∧ o d = true} : Finset G.Dart) =
        ({d | C.IsFwd d ∧ o d = false} : Finset G.Dart).image Dart.symm := by
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_image]
      constructor
      · rintro ⟨hdI, hon, hod⟩
        refine ⟨d.symm, ⟨?_, by rw [ho.1 d, hod]; rfl⟩, Dart.symm_symm d⟩
        rcases hon with hon | hon
        · exact absurd ((hI.face_fwd_iff hon (C.isFwd_outDart v₀ hv₀)).1 hdI) hin
        · exact hon
      · rintro ⟨d', ⟨hfw, hod⟩, rfl⟩
        refine ⟨?_, (C.onCycle_symm d').2 (Or.inl hfw), by rw [ho.1 d', hod]; rfl⟩
        exact (hI.iff_of_onCycle (Or.inl hfw)).2
          (fun h' => hin ((hI.face_fwd_iff hfw (C.isFwd_outDart v₀ hv₀)).1 h'))
    rw [hsymm, card_image_of_injective _ (Dart.symm_involutive.injective)] at h
    have hsplit := card_filter_add_card_filter_not (s := ({d | C.IsFwd d} : Finset G.Dart))
      (p := fun d => o d = true)
    simp only [filter_filter, Bool.not_eq_true] at hsplit
    rw [hfwd] at hsplit
    obtain ⟨k, hk⟩ := hC
    rw [Nat.odd_iff] at h ⊢
    omega

end RotationSystem

end Kasteleyn
