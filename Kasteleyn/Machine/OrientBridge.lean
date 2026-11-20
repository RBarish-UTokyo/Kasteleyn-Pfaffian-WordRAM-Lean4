module

public import Kasteleyn.Machine.Orient
public import Kasteleyn.Plane.Orientation

/-!
# Running the orientation program on a rotation system

A rotation system `M` on a finite graph is encoded as an input of `Orient.orient`: the faces are
numbered by `eF`, the darts are listed face by face (ordered by the key `(face index, eD x)`),
and the initial orientation of a dart `x` is `eD x < eD x.symm`. The input has
`4 + F + 3 S` words for `F` faces and `S` darts.

The encoding (`Kasteleyn.Orient.rotEnc` and the definitions it uses: `enc`, `pos`, `ofs`,
`dartAt`, ...) and the word bound `Kasteleyn.Orient.rotW` are defined in `Kasteleyn/Spec.lean`.

## Main results

* `Kasteleyn.Orient.isKasteleyn_of_isOrient`: the bits printed by the program, read back through
  the slot of each dart, form a Kasteleyn orientation of `M` with respect to the root face.
* `Kasteleyn.Orient.orient_rotationSystem`: **a Kasteleyn orientation of a connected rotation
  system in linear time**: the program halts within `36 F + 39 S + 27` steps.
-/

@[expose] public section

namespace Kasteleyn

namespace Orient

open Finset SimpleGraph WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### Inputs given by functions -/

theorem getD_ofFun {n : ℕ} {w : ℕ → ℕ} {j : ℕ} (hj : j < n) : (ofFun n w).getD j 0 = w j := by
  simp [ofFun, List.getD_eq_getElem?_getD, hj]

theorem getD_ofFun_ge {n : ℕ} {w : ℕ → ℕ} {j : ℕ} (hj : n ≤ j) : (ofFun n w).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [ofFun] using hj)]; rfl

section enc
variable {F S r : ℕ} {ofs tgt rev bit : ℕ → ℕ}

theorem length_enc : (enc F S r ofs tgt rev bit).length = 4 + F + 3 * S := by
  simp [enc, ofFun]

theorem nf_enc : nf (enc F S r ofs tgt rev bit) = F := by
  rw [nf, word, enc, getD_ofFun (by omega)]; simp [encWord]

theorem nd_enc : nd (enc F S r ofs tgt rev bit) = S := by
  rw [nd, word, enc, getD_ofFun (by omega)]; simp [encWord]

theorem root_enc : root (enc F S r ofs tgt rev bit) = r := by
  rw [root, word, enc, getD_ofFun (by omega)]; simp [encWord]

theorem off_enc {u : ℕ} (hu : u ≤ F) : off (enc F S r ofs tgt rev bit) u = ofs u := by
  rw [off, word, enc, getD_ofFun (by omega)]
  unfold encWord; split_ifs <;> first | omega | (congr 1; omega)

theorem tg_enc {i : ℕ} (hi : i < S) : tg (enc F S r ofs tgt rev bit) i = tgt i := by
  rw [tg, nf_enc, word, enc, getD_ofFun (by omega)]
  unfold encWord; split_ifs <;> first | omega | (congr 1; omega)

theorem rv_enc {i : ℕ} (hi : i < S) : rv (enc F S r ofs tgt rev bit) i = rev i := by
  rw [rv, nf_enc, word, enc, getD_ofFun (by omega)]
  unfold encWord; split_ifs <;> first | omega | (congr 1; omega)

theorem ini_enc {i : ℕ} (hi : i < S) : ini (enc F S r ofs tgt rev bit) i = bit i := by
  rw [ini, nf_enc, word, enc, getD_ofFun (by omega)]
  unfold encWord; split_ifs <;> first | omega | (congr 1; omega)

theorem word_enc_le {W : ℕ} (hF : F ≤ W) (hS : S ≤ W) (hr : r ≤ W) (ho : ∀ u, ofs u ≤ W)
    (ht : ∀ i, tgt i ≤ W) (hv : ∀ i, rev i ≤ W) (hb : ∀ i, bit i ≤ W) (j : ℕ) :
    word (enc F S r ofs tgt rev bit) j ≤ W := by
  rw [word, enc]
  rcases Nat.lt_or_ge j (4 + F + 3 * S) with hj | hj
  · rw [getD_ofFun hj]; unfold encWord; split_ifs <;> first | assumption | apply_assumption
  · rw [getD_ofFun_ge hj]; exact Nat.zero_le _

end enc

theorem mul_add_inj {a b c e n : ℕ} (hb : b < n) (he : e < n) (h : a * n + b = c * n + e) :
    a = c ∧ b = e := by
  have h1 : (a * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
  have h2 : (c * n + e) / n = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, zero_add]
  have hac : a = c := by rw [← h1, h, h2]
  subst hac
  exact ⟨rfl, by omega⟩

/-! ### The encoding of a rotation system -/

section rot

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (M : RotationSystem G) (eF : M.Face ≃ Fin (Fintype.card M.Face))
  (eD : G.Dart ≃ Fin (Fintype.card G.Dart))

variable {M eF eD}

theorem fi_lt (x : G.Dart) : fi M eF x < Fintype.card M.Face := (eF (M.face x)).2

theorem key_inj {x y : G.Dart} (h : key M eF eD x = key M eF eD y) : x = y :=
  eD.injective (Fin.ext (mul_add_inj (eD x).2 (eD y).2 h).2)

theorem key_lt_of_fi_lt {x y : G.Dart} (h : fi M eF x < fi M eF y) :
    key M eF eD x < key M eF eD y := by
  unfold key
  have h1 := Nat.mul_le_mul_right (Fintype.card G.Dart) (Nat.succ_le_of_lt h)
  have h2 := (eD x).2
  rw [Nat.succ_mul] at h1
  omega

theorem fi_le_of_key_lt {x y : G.Dart} (h : key M eF eD x < key M eF eD y) :
    fi M eF x ≤ fi M eF y := by
  by_contra h'
  exact absurd (key_lt_of_fi_lt (eD := eD) (by omega : fi M eF y < fi M eF x)) (by omega)

theorem pos_lt (x : G.Dart) : pos M eF eD x < Fintype.card G.Dart := by
  unfold pos
  refine (card_lt_card ⟨filter_subset _ _, fun h => ?_⟩).trans_eq card_univ
  have := h (mem_univ x)
  simp at this

theorem pos_lt_pos {x y : G.Dart} (h : key M eF eD x < key M eF eD y) :
    pos M eF eD x < pos M eF eD y := by
  unfold pos
  refine card_lt_card ⟨fun z hz => ?_, fun hs => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hz ⊢; omega
  · have := hs (by simp [h] : x ∈ filter (fun z => key M eF eD z < key M eF eD y) univ)
    simp at this

theorem pos_injective : Function.Injective (pos M eF eD) := by
  intro x y h
  rcases lt_trichotomy (key M eF eD x) (key M eF eD y) with h' | h' | h'
  · exact absurd h (pos_lt_pos h').ne
  · exact key_inj h'
  · exact absurd h (pos_lt_pos h').ne'

/-- The slots as an equivalence. -/
noncomputable def eS : G.Dart ≃ Fin (Fintype.card G.Dart) :=
  Equiv.ofBijective (fun x => ⟨pos M eF eD x, pos_lt x⟩) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨fun x y h => pos_injective (congrArg Fin.val h), by simp⟩

theorem eS_apply (x : G.Dart) : (eS (M := M) (eF := eF) (eD := eD) x : ℕ) = pos M eF eD x := rfl

theorem pos_eS_symm (i : Fin (Fintype.card G.Dart)) :
    pos M eF eD ((eS (M := M) (eF := eF) (eD := eD)).symm i) = i := by
  rw [← eS_apply, Equiv.apply_symm_apply]

theorem ofs_mono {u v : ℕ} (h : u ≤ v) : ofs M eF u ≤ ofs M eF v :=
  card_le_card fun y hy => by simp only [mem_filter, mem_univ, true_and] at hy ⊢; omega

theorem ofs_le (u : ℕ) : ofs M eF u ≤ Fintype.card G.Dart :=
  (card_le_card (subset_univ _)).trans_eq card_univ

theorem ofs_zero : ofs M eF 0 = 0 := by simp [ofs]

theorem ofs_last : ofs M eF (Fintype.card M.Face) = Fintype.card G.Dart := by
  unfold ofs
  rw [filter_true_of_mem fun y _ => fi_lt y, card_univ]

theorem ofs_le_pos (x : G.Dart) : ofs M eF (fi M eF x) ≤ pos M eF eD x :=
  card_le_card fun y hy => by
    simp only [mem_filter, mem_univ, true_and] at hy ⊢; exact key_lt_of_fi_lt hy

theorem pos_lt_ofs (x : G.Dart) : pos M eF eD x < ofs M eF (fi M eF x + 1) := by
  unfold pos ofs
  refine card_lt_card ⟨fun y hy => ?_, fun hs => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hy ⊢
    have := fi_le_of_key_lt hy; omega
  · have := hs (by simp : x ∈ filter (fun z => fi M eF z < fi M eF x + 1) univ)
    simp at this

theorem eq_of_ofs {a b i : ℕ} (ha : ofs M eF a ≤ i ∧ i < ofs M eF (a + 1))
    (hb : ofs M eF b ≤ i ∧ i < ofs M eF (b + 1)) : a = b := by
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := ofs_mono (M := M) (eF := eF) (by omega : a + 1 ≤ b); omega
  · have := ofs_mono (M := M) (eF := eF) (by omega : b + 1 ≤ a); omega

theorem pos_dartAt {i : ℕ} (hi : i < Fintype.card G.Dart) :
    pos M eF eD (dartAt (M := M) (eF := eF) (eD := eD) i hi) = i :=
  @Classical.epsilon_spec G.Dart (fun x => pos M eF eD x = i) ⟨_, pos_eS_symm ⟨i, hi⟩⟩

theorem dartAt_pos (x : G.Dart) (h : pos M eF eD x < Fintype.card G.Dart) :
    dartAt (M := M) (eF := eF) (eD := eD) (pos M eF eD x) h = x :=
  pos_injective (pos_dartAt h)

theorem inFace_pos (f₀ : M.Face) (x : G.Dart) :
    InFace (rotEnc M eF eD f₀) (fi M eF x) (pos M eF eD x) := by
  unfold InFace rotEnc
  rw [off_enc (fi_lt x).le, off_enc (fi_lt x)]
  exact ⟨ofs_le_pos x, pos_lt_ofs x⟩

theorem tg_pos (f₀ : M.Face) (x : G.Dart) :
    tg (rotEnc M eF eD f₀) (pos M eF eD x) = fi M eF x.symm := by
  unfold rotEnc; rw [tg_enc (pos_lt x), dif_pos (pos_lt x), dartAt_pos]

theorem rv_pos (f₀ : M.Face) (x : G.Dart) :
    rv (rotEnc M eF eD f₀) (pos M eF eD x) = pos M eF eD x.symm := by
  unfold rotEnc; rw [rv_enc (pos_lt x), dif_pos (pos_lt x), dartAt_pos]

theorem ini_pos (f₀ : M.Face) (x : G.Dart) :
    ini (rotEnc M eF eD f₀) (pos M eF eD x) = if ini0 eD x then 1 else 0 := by
  unfold rotEnc; rw [ini_enc (pos_lt x), dif_pos (pos_lt x), dartAt_pos]

theorem ini0_symm (x : G.Dart) : ini0 eD x.symm = !ini0 eD x := by
  unfold ini0
  rw [Dart.symm_symm]
  have hne : (eD x : ℕ) ≠ eD x.symm := fun h =>
    x.symm_ne (eD.injective (Fin.ext h)).symm
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · simp [h, h.not_gt]
  · simp [h, h.not_gt]

theorem exists_pos {i : ℕ} (hi : i < Fintype.card G.Dart) : ∃ x : G.Dart, pos M eF eD x = i :=
  ⟨_, pos_dartAt (M := M) (eF := eF) (eD := eD) hi⟩

/-- Faces and slots: slot `i` lies in face `u` iff the dart of slot `i` has face index `u`. -/
theorem inFace_iff (f₀ : M.Face) (x : G.Dart) {u : ℕ} (hu : u < Fintype.card M.Face) :
    InFace (rotEnc M eF eD f₀) u (pos M eF eD x) ↔ fi M eF x = u := by
  constructor
  · intro h
    have h' := inFace_pos (M := M) (eF := eF) (eD := eD) f₀ x
    unfold InFace rotEnc at h h'
    rw [off_enc hu.le, off_enc hu] at h
    rw [off_enc (fi_lt x).le, off_enc (fi_lt x)] at h'
    exact eq_of_ofs h' h
  · rintro rfl; exact inFace_pos f₀ x

theorem oEnc_rotEnc (hG : G.Connected) (f₀ : M.Face) :
    OEnc (rotEnc M eF eD f₀) (rotW M) := by
  have hF := Fintype.card_pos_iff.2 ⟨f₀⟩
  have hroot : root (rotEnc M eF eD f₀) = eF f₀ := root_enc
  have hnf : nf (rotEnc M eF eD f₀) = Fintype.card M.Face := nf_enc
  have hnd : nd (rotEnc M eF eD f₀) = Fintype.card G.Dart := nd_enc
  -- every slot below `S` is the slot of a dart
  have hslot : ∀ {P : ℕ → Prop}, (∀ x, P (pos M eF eD x)) → ∀ i < Fintype.card G.Dart, P i :=
    fun h i hi => by obtain ⟨x, rfl⟩ := exists_pos (M := M) (eF := eF) (eD := eD) hi; exact h x
  refine ⟨fun j => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rotEnc rotW
    refine word_enc_le (W := 4 * Fintype.card M.Face + 5 * Fintype.card G.Dart + 8) (by omega)
      (by omega) (by have := (eF f₀).2; omega) (fun u => (ofs_le u).trans (by omega))
      (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · split_ifs
      · exact (fi_lt _).le.trans (by omega)
      · omega
    · split_ifs
      · exact (pos_lt _).le.trans (by omega)
      · omega
    · split_ifs <;> omega
  · rw [hnf, hnd]; unfold rotW; omega
  · unfold rotEnc; rw [off_enc (Nat.zero_le _), ofs_zero]
  · rw [hnf, hnd]; unfold rotEnc; rw [off_enc le_rfl, ofs_last]
  · intro u hu; rw [hnf] at hu
    unfold rotEnc; rw [off_enc hu.le, off_enc hu]; exact ofs_mono (Nat.le_succ u)
  · rw [hroot, hnf]; exact (eF f₀).2
  · rw [hnd, hnf]; exact hslot fun x => by rw [tg_pos]; exact fi_lt _
  · rw [hnd]; exact hslot fun x => by rw [rv_pos]; exact pos_lt _
  · intro u hu i hi
    rw [hnf] at hu
    have hiS : i < Fintype.card G.Dart := by
      have := hi.2; unfold rotEnc at this; rw [off_enc hu] at this
      exact this.trans_le (ofs_le _)
    obtain ⟨x, rfl⟩ := exists_pos (M := M) (eF := eF) (eD := eD) hiS
    rw [tg_pos, rv_pos]; exact inFace_pos f₀ _
  · intro u hu i hi
    rw [hnf] at hu
    have hiS : i < Fintype.card G.Dart := by
      have := hi.2; unfold rotEnc at this; rw [off_enc hu] at this
      exact this.trans_le (ofs_le _)
    obtain ⟨x, rfl⟩ := exists_pos (M := M) (eF := eF) (eD := eD) hiS
    rw [rv_pos, tg_pos, Dart.symm_symm]; exact (inFace_iff f₀ x hu).1 hi
  · rw [hnd]; exact hslot fun x => by rw [rv_pos, rv_pos, Dart.symm_symm]
  · rw [hnd]; exact hslot fun x => by rw [ini_pos]; split_ifs <;> omega
  · rw [hnd]; exact hslot fun x => by
      rw [rv_pos, ini_pos, ini_pos, ini0_symm]; cases ini0 eD x <;> rfl
  · -- the dual graph is connected
    intro v hv
    rw [hnf] at hv
    rw [hroot]
    let g : M.Face → Prop := fun f => Relation.ReflTransGen (DArc (rotEnc M eF eD f₀))
      (eF f₀ : ℕ) (eF f : ℕ)
    have harc : ∀ x : G.Dart, DArc (rotEnc M eF eD f₀) (fi M eF x) (fi M eF x.symm) := fun x =>
      ⟨by rw [hnf]; exact fi_lt x, _, inFace_pos f₀ x, tg_pos f₀ x⟩
    have hg : ∀ x : G.Dart, g (M.face x.symm) = g (M.face x) := fun x => propext
      ⟨fun h => h.tail (by have := harc x.symm; rwa [Dart.symm_symm] at this),
        fun h => h.tail (harc x)⟩
    have := M.face_const hG hg f₀ (eF.symm ⟨v, hv⟩)
    have h0 : g f₀ := Relation.ReflTransGen.refl
    rw [this] at h0
    simpa [g] using h0

/-- **The output of the program is a Kasteleyn orientation.** -/
theorem isKasteleyn_of_isOrient {f₀ : M.Face} {o : ℕ → ℕ}
    (h : IsOrient (rotEnc M eF eD f₀) o) :
    M.IsKasteleyn (fun x => decide (o (pos M eF eD x) = 1)) f₀ := by
  obtain ⟨hb, ha, hodd⟩ := h
  have hnd : nd (rotEnc M eF eD f₀) = Fintype.card G.Dart := nd_enc
  have hnf : nf (rotEnc M eF eD f₀) = Fintype.card M.Face := nf_enc
  refine ⟨fun x => ?_, fun f hf => ?_⟩
  · have h1 := ha _ (hnd ▸ pos_lt (M := M) (eF := eF) (eD := eD) x)
    have h2 := hb _ (hnd ▸ pos_lt (M := M) (eF := eF) (eD := eD) x)
    rw [rv_pos] at h1
    simp only [h1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with e | e <;> simp [e]
  · have hu : (eF f : ℕ) < Fintype.card M.Face := (eF f).2
    have hne : (eF f : ℕ) ≠ root (rotEnc M eF eD f₀) := by
      have hroot : root (rotEnc M eF eD f₀) = eF f₀ := root_enc
      rw [hroot]; intro e; exact hf (eF.injective (Fin.ext e))
    have hO := hodd _ (by rw [hnf]; exact hu) hne
    -- the slots of face `f` are the slots of its darts
    have himg : Ico (off (rotEnc M eF eD f₀) (eF f)) (off (rotEnc M eF eD f₀) (eF f + 1)) =
        (filter (fun x => M.face x = f) univ).image (pos M eF eD) := by
      ext i
      simp only [mem_Ico, mem_image, mem_filter, mem_univ, true_and]
      constructor
      · intro hi
        have hiS : i < Fintype.card G.Dart := by
          have := hi.2; unfold rotEnc at this; rw [off_enc hu] at this
          exact this.trans_le (ofs_le _)
        obtain ⟨x, rfl⟩ := exists_pos (M := M) (eF := eF) (eD := eD) hiS
        refine ⟨x, ?_, rfl⟩
        have := (inFace_iff (eD := eD) f₀ x hu).1 hi
        exact eF.injective (Fin.ext this)
      · rintro ⟨x, rfl, rfl⟩
        exact inFace_pos f₀ x
    unfold count at hO
    rw [himg, sum_image fun x _ y _ e => pos_injective e] at hO
    have hc : ∑ x ∈ filter (fun x => M.face x = f) univ, o (pos M eF eD x) =
        M.cwCount (fun x => decide (o (pos M eF eD x) = 1)) f := by
      rw [RotationSystem.cwCount, card_filter, sum_filter]
      refine sum_congr rfl fun x _ => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1
        (hb _ (hnd ▸ pos_lt (M := M) (eF := eF) (eD := eD) x)) with e | e <;>
        by_cases hx : M.face x = f <;> simp [e, hx]
    rwa [hc] at hO

/-- **A Kasteleyn orientation of a connected rotation system in linear time.** With `F` faces
and `S` darts the input has `4 + F + 3 S` words, and the program halts within `36 F + 39 S + 27`
steps. It prints one bit per slot, and the bit in the slot of each dart gives a Kasteleyn
orientation with respect to `f₀`. -/
theorem orient_rotationSystem (hG : G.Connected) (f₀ : M.Face) :
    (rotEnc M eF eD f₀).length = 4 + Fintype.card M.Face + 3 * Fintype.card G.Dart ∧
    ∃ o : ℕ → ℕ, M.IsKasteleyn (fun x => decide (o (pos M eF eD x) = 1)) f₀ ∧
      RunsWithin (compile orient 0 ++ [Instr.halt]) (inp (rotEnc M eF eD f₀)) (rotW M)
        (36 * Fintype.card M.Face + 39 * Fintype.card G.Dart + 27)
        ((List.range (Fintype.card G.Dart)).map o) := by
  refine ⟨length_enc, ?_⟩
  obtain ⟨o, hO, hR⟩ := orient_runsWithin (oEnc_rotEnc (eF := eF) (eD := eD) hG f₀)
  have hnf : nf (rotEnc M eF eD f₀) = Fintype.card M.Face := nf_enc
  have hnd : nd (rotEnc M eF eD f₀) = Fintype.card G.Dart := nd_enc
  rw [hnf, hnd] at hR
  exact ⟨o, isKasteleyn_of_isOrient hO, hR⟩

end rot

end Orient

end Kasteleyn
