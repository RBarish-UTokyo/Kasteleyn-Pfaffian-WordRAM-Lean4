module

public import WordRAM
public import Kasteleyn.Spec
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# A Kasteleyn orientation in linear time on the machine

The program `Orient.orient` reads a plane graph through its faces: `F` faces, `S` darts listed
face by face (the darts of face `u` are the slots `off u ≤ i < off (u + 1)`), and for each dart
`i` the face `tg i` of its reverse, the slot `rv i` of its reverse and an initial orientation
bit `ini i` (with `ini (rv i) = 1 - ini i`). It prints orientation bits `o i` with
`o (rv i) = 1 - o i` such that every face other than the root face `r` has an odd number of
darts with bit `1` (`Orient.orient_runsWithin`), within `O(F + S)` steps.

The algorithm: a breadth-first search of the dual graph from `r` records for every other face
`v` the dart `par v` of `v` towards its parent; then the faces are processed in the reverse order
of the search: for `v`, the bit of `par v` (and of its reverse) is chosen so that the count of
`v` is odd. Later steps only change darts of faces that come earlier in the search, so the count
of `v` stays odd. This is the classical construction of Kasteleyn (1967) for plane graphs;
`Kasteleyn.RotationSystem.kasteleynOrientation` is a construction of the same kind.

Input: `[F, S, r, off 0, …, off F, tg 0, rv 0, ini 0, tg 1, …]`. Memory: the bits at `0 … S - 1`,
visit marks at `S + v`, parents at `S + F + v`, the queue at `S + 2F + k`.
-/

@[expose] public section

namespace Kasteleyn

namespace Orient

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The input -/

/-! The input `inp d` of a run on the words `d` is defined in `Kasteleyn/Spec.lean`. -/

/-- The words of the input. -/
def word (d : List ℕ) (i : ℕ) : ℕ := d.getD i 0
def nf (d : List ℕ) : ℕ := word d 0
def nd (d : List ℕ) : ℕ := word d 1
def root (d : List ℕ) : ℕ := word d 2
def off (d : List ℕ) (u : ℕ) : ℕ := word d (3 + u)
def tg (d : List ℕ) (i : ℕ) : ℕ := word d (4 + nf d + 3 * i)
def rv (d : List ℕ) (i : ℕ) : ℕ := word d (5 + nf d + 3 * i)
def ini (d : List ℕ) (i : ℕ) : ℕ := word d (6 + nf d + 3 * i)

/-- The darts of face `u` are the slots `off u ≤ i < off (u + 1)`. -/
def InFace (d : List ℕ) (u i : ℕ) : Prop := off d u ≤ i ∧ i < off d (u + 1)

/-- An arc of the dual graph: a dart of `u` whose reverse lies on `v`. -/
def DArc (d : List ℕ) (u v : ℕ) : Prop := u < nf d ∧ ∃ i, InFace d u i ∧ tg d i = v

/-- Well-formed inputs. -/
structure OEnc (d : List ℕ) (W : ℕ) : Prop where
  word_le : ∀ i, word d i ≤ W
  size : 4 * nf d + 2 * nd d + 3 * nd d + 8 ≤ W
  off_zero : off d 0 = 0
  off_last : off d (nf d) = nd d
  off_mono : ∀ u < nf d, off d u ≤ off d (u + 1)
  root_lt : root d < nf d
  tg_lt : ∀ i < nd d, tg d i < nf d
  rv_lt : ∀ i < nd d, rv d i < nd d
  rv_face : ∀ u < nf d, ∀ i, InFace d u i → InFace d (tg d i) (rv d i)
  tg_rv : ∀ u < nf d, ∀ i, InFace d u i → tg d (rv d i) = u
  rv_rv : ∀ i < nd d, rv d (rv d i) = i
  ini_le : ∀ i < nd d, ini d i ≤ 1
  ini_rv : ∀ i < nd d, ini d (rv d i) = 1 - ini d i
  conn : ∀ v < nf d, Relation.ReflTransGen (DArc d) (root d) v

/-- The count of a face for bits `o`. -/
def count (d : List ℕ) (o : ℕ → ℕ) (u : ℕ) : ℕ := ∑ i ∈ Ico (off d u) (off d (u + 1)), o i

/-- What the output satisfies: bits, antisymmetric, odd counts off the root. -/
def IsOrient (d : List ℕ) (o : ℕ → ℕ) : Prop :=
  (∀ i < nd d, o i ≤ 1) ∧ (∀ i < nd d, o (rv d i) = 1 - o i) ∧
    ∀ u < nf d, u ≠ root d → Odd (count d o u)

/-! ### The program -/

/-- Constants: `r1 = 1`, `r2 = F`, `r3 = S`, `r4 = 4 + F`, `r5 = 3`, `r6 = S + F`,
`r7 = S + 2F`, `r8 = r`, `r20 = 2`. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .constN 20 2, .readIn 8 20,
  .constN 5 3, .addN 4 2 5, .addN 4 4 1, .addN 6 3 2, .addN 7 6 2, .copyN 9 0]

/-- Phase 1, one dart `r9`: its initial bit. -/
def iniStep : Stmt := block [.mulN 10 9 5, .addN 10 10 4, .addN 10 10 20, .readIn 11 10,
  .storeN 9 11, .addN 9 9 1]

/-- Phase 2, the start of the search: mark and enqueue the root. -/
def bfsStart : Stmt := block [.addN 10 3 8, .storeN 10 1, .storeN 7 8, .copyN 11 1, .copyN 12 0]

/-- Phase 2, dequeue `r13` and read its range of darts `r14 … r15`. -/
def deq : Stmt := block [.addN 10 7 12, .loadN 13 10, .addN 12 12 1, .addN 10 13 5,
  .readIn 14 10, .addN 10 10 1, .readIn 15 10]

/-- Phase 2, one dart `r14` of `r13`: visit the face across if new. -/
def slot : Stmt :=
  .seq (block [.mulN 10 14 5, .addN 10 10 4, .readIn 16 10, .addN 10 10 1, .readIn 17 10,
      .addN 10 3 16, .loadN 9 10])
    (.seq (.ifLtN 0 9 .skip (block [.storeN 10 1, .addN 10 6 16, .storeN 10 17, .addN 10 7 11,
        .storeN 10 16, .addN 11 11 1]))
      (.instr (.addN 14 14 1)))

/-- Phase 3, one dart `r14` of the face being fixed: count it unless it is the parent dart
`r23`. -/
def cnt : Stmt :=
  .seq (.ifLtN 14 23 (block [.loadN 9 14, .addN 18 18 9])
      (.ifLtN 23 14 (block [.loadN 9 14, .addN 18 18 9]) .skip))
    (.instr (.addN 14 14 1))

/-- Phase 3, the face `Q[r22 - 1]`: fix its parent dart. -/
def fix : Stmt :=
  .seq (block [.subN 22 22 1, .addN 10 7 22, .loadN 16 10, .addN 10 6 16, .loadN 23 10,
      .addN 10 16 5, .readIn 14 10, .addN 10 10 1, .readIn 15 10, .copyN 18 0])
    (.seq (.whileLtN 14 15 cnt)
      (block [.addN 18 18 1, .modN 18 18 20, .storeN 23 18, .mulN 10 23 5, .addN 10 10 4,
        .addN 10 10 1, .readIn 17 10, .subN 9 1 18, .storeN 17 9]))

/-- Phase 4, print the bit of dart `r9`. -/
def outStep : Stmt := block [.loadN 10 9, .outN 10, .addN 9 9 1]

/-- **The Kasteleyn orientation.** -/
def orient : Stmt :=
  .seq setup <| .seq (.whileLtN 9 3 iniStep) <| .seq bfsStart <|
  .seq (.whileLtN 12 11 (.seq deq (.whileLtN 14 15 slot))) <|
  .seq (.instr (.copyN 22 11)) <| .seq (.whileLtN 1 22 fix) <|
  .seq (.instr (.copyN 9 0)) (.whileLtN 9 3 outStep)

/-! ### The constant registers -/

/-- The constant registers. -/
def ORegs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = nf d ∧ c.nreg 3 = nd d ∧ c.nreg 4 = 4 + nf d ∧
    c.nreg 5 = 3 ∧ c.nreg 6 = nd d + nf d ∧ c.nreg 7 = nd d + 2 * nf d ∧ c.nreg 8 = root d ∧
    c.nreg 20 = 2

/-- The constant registers are unchanged. -/
def KeepsO (c c' : Config) : Prop :=
  ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 20 →
    c'.nreg r = c.nreg r

theorem oregs_of {d : List ℕ} {c c' : Config} (hR : ORegs d c) (h : KeepsO c c') : ORegs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-! ### Phase 1: the initial bits -/

/-- The state of phase 1. -/
structure I1 (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ORegs d c
  r9 : c.nreg 9 ≤ nd d
  bits : ∀ i < c.nreg 9, c.nmem i = ini d i
  zero : ∀ a, nd d ≤ a → c.nmem a = 0
  out : c.output = []

section phase1
variable {d : List ℕ} {W : ℕ}

theorem setup_exec (he : OEnc d W) :
    ∃ c' k, Exec (inp d) W setup initConfig c' k ∧ I1 d W c' ∧ k = 11 := by
  have hs := he.size
  have hw : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  unfold setup
  exec_block
  · omega
  · exact he.word_le _
  · exact he.word_le _
  · omega
  · exact he.word_le _
  · omega
  · config_simp; simp only [initConfig, inp]; unfold nf word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nf word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nf nd word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nf nd word at hs; omega
  refine ⟨⟨‹_›, ?_, ?_, fun i hi => ?_, fun a _ => ?_, ?_⟩, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp [initConfig, inp, nf, nd, root, word] <;> omega
  · config_simp; simp [initConfig]
  · config_simp at hi; simp [initConfig] at hi
  · config_simp; simp [initConfig]
  · config_simp; simp [initConfig]

theorem iniStep_exec (he : OEnc d W) (c : Config) (hI : I1 d W c) (hlt : c.nreg 9 < c.nreg 3) :
    ∃ c' k, Exec (inp d) W iniStep c c' k ∧ I1 d W c' ∧
      (nd d - c'.nreg 9) * 8 + k + 2 ≤ (nd d - c.nreg 9) * 8 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hI.regs
  rw [h3] at hlt
  have hidx : (inp d).data.getD (c.nreg 9 * c.nreg 5 + c.nreg 4 + c.nreg 20) 0 = ini d (c.nreg 9) := by
    simp only [inp, ini, word, h5, h4, h20]; congr 1; omega
  unfold iniStep
  exec_block
  · config_simp; rw [h5]; omega
  · config_simp; rw [h5, h4]; omega
  · config_simp; rw [h5, h4, h20]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h1]; omega
  simp only [hidx] at *
  refine ⟨⟨‹_›, oregs_of hI.regs fun r hr => ?_, by config_simp; rw [h1]; omega, fun i hi => ?_,
    fun a ha => ?_, by config_simp; exact hI.out⟩, by config_simp; rw [h1]; omega⟩
  · config_simp
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp at hi; config_simp; rw [h1] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.bits i hi
    · rw [upd_same]
  · config_simp; rw [upd_other _ _ _ (by omega)]; exact hI.zero a ha

end phase1

/-! ### Phase 2: the search of the dual graph -/

/-- Visit marks, parents and the queue. -/
def vis (d : List ℕ) (c : Config) (v : ℕ) : ℕ := c.nmem (nd d + v)
def par (d : List ℕ) (c : Config) (v : ℕ) : ℕ := c.nmem (nd d + nf d + v)
def qu (d : List ℕ) (c : Config) (k : ℕ) : ℕ := c.nmem (nd d + 2 * nf d + k)

/-- The state of the search. -/
structure CB (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ORegs d c
  out : c.output = []
  bits : ∀ i < nd d, c.nmem i = ini d i
  head_le : c.nreg 12 ≤ c.nreg 11
  q_lt : ∀ k < c.nreg 11, qu d c k < nf d
  q_inj : ∀ k < c.nreg 11, ∀ l < c.nreg 11, qu d c k = qu d c l → k = l
  q0 : 0 < c.nreg 11 ∧ qu d c 0 = root d
  vis01 : ∀ v < nf d, vis d c v = 0 ∨ vis d c v = 1
  vis_iff : ∀ v < nf d, vis d c v = 1 ↔ ∃ k < c.nreg 11, qu d c k = v
  par_ok : ∀ k, 1 ≤ k → k < c.nreg 11 → InFace d (qu d c k) (par d c (qu d c k)) ∧
    ∃ k' < k, tg d (par d c (qu d c k)) = qu d c k'

/-- A face all of whose darts lead to visited faces. -/
def Scanned (d : List ℕ) (c : Config) (u : ℕ) : Prop := ∀ i, InFace d u i → vis d c (tg d i) = 1

/-- Between dequeues. -/
structure IB (d : List ℕ) (W : ℕ) (c : Config) : Prop extends CB d W c where
  closed : ∀ k < c.nreg 12, Scanned d c (qu d c k)

/-- While scanning the darts of the dequeued face `r13`. -/
structure JB (d : List ℕ) (W : ℕ) (c : Config) : Prop extends CB d W c where
  head_pos : 0 < c.nreg 12
  cur : c.nreg 13 = qu d c (c.nreg 12 - 1)
  r15 : c.nreg 15 = off d (c.nreg 13 + 1)
  r14_ge : off d (c.nreg 13) ≤ c.nreg 14
  r14_le : c.nreg 14 ≤ c.nreg 15
  closed : ∀ k, k + 1 < c.nreg 12 → Scanned d c (qu d c k)
  closed_cur : ∀ i, off d (c.nreg 13) ≤ i → i < c.nreg 14 → vis d c (tg d i) = 1

section phase2
variable {d : List ℕ} {W : ℕ}

theorem off_le_off (he : OEnc d W) {u v : ℕ} (huv : u ≤ v) (hv : v ≤ nf d) : off d u ≤ off d v := by
  induction v with
  | zero => obtain rfl : u = 0 := by omega
            exact le_rfl
  | succ v ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le huv) with h | h
    · exact (ih (by omega) (by omega)).trans (he.off_mono v (by omega))
    · rw [h]

theorem inFace_lt (he : OEnc d W) {u i : ℕ} (hu : u < nf d) (h : InFace d u i) : i < nd d := by
  have := off_le_off he (u := u + 1) (v := nf d) hu le_rfl
  rw [he.off_last] at this; exact lt_of_lt_of_le h.2 this

/-- Darts of distinct faces are distinct. -/
theorem inFace_unique (he : OEnc d W) {u v i : ℕ} (hu : u < nf d) (hv : v < nf d)
    (h1 : InFace d u i) (h2 : InFace d v i) : u = v := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := off_le_off he (u := u + 1) (v := v) h hv.le; have := h1.2; have := h2.1; omega
  · have := off_le_off he (u := v + 1) (v := u) h hu.le; have := h2.2; have := h1.1; omega

theorem CB.tail_lt {c : Config} (hI : CB d W c) {v : ℕ} (hv : v < nf d)
    (hnot : ∀ k < c.nreg 11, qu d c k ≠ v) : c.nreg 11 < nf d := by
  classical
  have h := Finset.card_le_card_of_injOn (qu d c) (s := range (c.nreg 11))
    (t := (range (nf d)).erase v)
    (fun k hk => by
      simp only [coe_range, Set.mem_Iio] at hk
      simp only [coe_erase, coe_range, Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨hI.q_lt k hk, hnot k hk⟩)
    (fun k hk l hl e => hI.q_inj k (by simpa using hk) l (by simpa using hl) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hv), card_range] at h
  omega

theorem CB.tail_le {c : Config} (hI : CB d W c) : c.nreg 11 ≤ nf d := by
  classical
  have h := Finset.card_le_card_of_injOn (qu d c) (s := range (c.nreg 11)) (t := range (nf d))
    (fun k hk => by simp only [coe_range, Set.mem_Iio] at hk ⊢; exact hI.q_lt k hk)
    (fun k hk l hl e => hI.q_inj k (by simpa using hk) l (by simpa using hl) e)
  simpa using h

/-- The scratch registers of the search. -/
def KeepsB (c c' : Config) : Prop :=
  ∀ r, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 →
    c'.nreg r = c.nreg r

theorem keepsO_of_keepsB {c c' : Config} (h : KeepsB c c') : KeepsO c c' := fun r hr =>
  h r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-- A dart to a visited face: skip it. -/
theorem JB.next_skip {c c' : Config} (hJ : JB d W c) (hi : c.nreg 14 < c.nreg 15)
    (hv : vis d c (tg d (c.nreg 14)) = 1) (hwb : WordsBounded W c') (hK : KeepsB c c')
    (h11 : c'.nreg 11 = c.nreg 11) (h12 : c'.nreg 12 = c.nreg 12) (h13 : c'.nreg 13 = c.nreg 13)
    (h14 : c'.nreg 14 = c.nreg 14 + 1) (h15 : c'.nreg 15 = c.nreg 15)
    (hout : c'.output = c.output) (hmem : c'.nmem = c.nmem) : JB d W c' := by
  have hvis : vis d c' = vis d c := by funext v; simp [vis, hmem]
  have hpar : par d c' = par d c := by funext v; simp [par, hmem]
  have hqu : qu d c' = qu d c := by funext v; simp [qu, hmem]
  refine ⟨⟨hwb, oregs_of hJ.regs (keepsO_of_keepsB hK), hout.trans hJ.out,
    fun i hi' => by rw [hmem]; exact hJ.bits i hi', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals simp only [hvis, hpar, hqu, h11, h12, h13, h14, h15, Scanned]
  · exact hJ.head_le
  · exact hJ.q_lt
  · exact hJ.q_inj
  · exact hJ.q0
  · exact hJ.vis01
  · exact hJ.vis_iff
  · exact hJ.par_ok
  · exact hJ.head_pos
  · exact hJ.cur
  · exact hJ.r15
  · have := hJ.r14_ge; omega
  · omega
  · exact hJ.closed
  · intro i h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hJ.closed_cur i h1 h2
    · exact hv

/-- A dart to a new face: mark it, record its parent dart, enqueue it. -/
theorem JB.next_enq (he : OEnc d W) {c c' : Config} (hJ : JB d W c) (hi : c.nreg 14 < c.nreg 15)
    (hv : vis d c (tg d (c.nreg 14)) = 0) (hwb : WordsBounded W c') (hK : KeepsB c c')
    (h11 : c'.nreg 11 = c.nreg 11 + 1) (h12 : c'.nreg 12 = c.nreg 12) (h13 : c'.nreg 13 = c.nreg 13)
    (h14 : c'.nreg 14 = c.nreg 14 + 1) (h15 : c'.nreg 15 = c.nreg 15)
    (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd (upd c.nmem (nd d + tg d (c.nreg 14)) 1)
      (nd d + nf d + tg d (c.nreg 14)) (rv d (c.nreg 14))) (nd d + 2 * nf d + c.nreg 11)
      (tg d (c.nreg 14))) : JB d W c' := by
  have hhp := hJ.head_pos; have hhl := hJ.head_le
  have hu := hJ.q_lt _ (show c.nreg 12 - 1 < c.nreg 11 by omega)
  rw [← hJ.cur] at hu
  have hiF : InFace d (c.nreg 13) (c.nreg 14) := ⟨hJ.r14_ge, hJ.r15 ▸ hi⟩
  have hin := inFace_lt he hu hiF
  generalize hgv : tg d (c.nreg 14) = v at hv hmem
  have hvn : v < nf d := hgv ▸ he.tg_lt _ hin
  have hnot : ∀ k < c.nreg 11, qu d c k ≠ v := fun k hk e => by
    have := (hJ.vis_iff v hvn).2 ⟨k, hk, e⟩; omega
  have htl := hJ.tail_lt hvn hnot
  have hvis : ∀ x < nf d, vis d c' x = if x = v then 1 else vis d c x := fun x hx => by
    simp only [vis, hmem, upd_apply]; split_ifs <;> first | omega | rfl
  have hpar : ∀ x < nf d, par d c' x = if x = v then rv d (c.nreg 14) else par d c x := fun x hx => by
    simp only [par, hmem, upd_apply]; split_ifs <;> first | omega | rfl
  have hqu : ∀ k < nf d, qu d c' k = if k = c.nreg 11 then v else qu d c k := fun k hk => by
    simp only [qu, hmem, upd_apply]; split_ifs <;> first | omega | rfl
  have hqu_lt : ∀ k < c.nreg 11, qu d c' k = qu d c k := fun k hk => by
    rw [hqu k (by omega)]; simp [show k ≠ c.nreg 11 by omega]
  have hvis_ge : ∀ x < nf d, vis d c x = 1 → vis d c' x = 1 := fun x hx h => by
    rw [hvis x hx]; split_ifs <;> simp [h]
  refine ⟨⟨hwb, oregs_of hJ.regs (keepsO_of_keepsB hK), hout.trans hJ.out, fun i hi' => ?_,
    by rw [h11, h12]; omega, fun k hk => ?_, fun k hk l hl e => ?_, ?_, fun x hx => ?_,
    fun x hx => ?_, fun k hk1 hk2 => ?_⟩, by rw [h12]; exact hhp, ?_, by rw [h15, h13]; exact hJ.r15,
    by rw [h14, h13]; have := hJ.r14_ge; omega, by rw [h14, h15]; omega, fun k hk => ?_,
    fun i h1 h2 => ?_⟩
  · rw [hmem, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact hJ.bits i hi'
  · rw [h11] at hk; rw [hqu k (by omega)]; split_ifs
    · exact hvn
    · exact hJ.q_lt k (by omega)
  · rw [h11] at hk hl
    rw [hqu k (by omega), hqu l (by omega)] at e
    split_ifs at e with h1 h2 h2
    · omega
    · exact absurd e.symm (hnot l (by omega))
    · exact absurd e (hnot k (by omega))
    · exact hJ.q_inj k (by omega) l (by omega) e
  · rw [h11]; refine ⟨by omega, ?_⟩; rw [hqu_lt 0 hJ.q0.1]; exact hJ.q0.2
  · rw [hvis x hx]; split_ifs
    · right; rfl
    · exact hJ.vis01 x hx
  · rw [hvis x hx, h11]
    split_ifs with hxv
    · subst hxv; simp only [true_iff]; exact ⟨c.nreg 11, by omega, by rw [hqu _ htl]; simp⟩
    · rw [hJ.vis_iff x hx]
      constructor
      · rintro ⟨k, hk, e⟩; exact ⟨k, by omega, by rw [hqu_lt k hk]; exact e⟩
      · rintro ⟨k, hk, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact ⟨k, hk, by rw [← hqu_lt k hk]; exact e⟩
        · rw [hqu _ htl] at e; simp at e; exact absurd e.symm hxv
  · rw [h11] at hk2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk2 | rfl
    · rw [hqu_lt k hk2, hpar _ (hJ.q_lt k hk2)]
      simp only [show qu d c k ≠ v from hnot k hk2, ↓reduceIte]
      obtain ⟨a, k', hk', b⟩ := hJ.par_ok k hk1 hk2
      exact ⟨a, k', hk', by rw [hqu_lt k' (by omega)]; exact b⟩
    · rw [hqu _ htl]; simp only [↓reduceIte]
      rw [hpar _ hvn]; simp only [↓reduceIte]
      refine ⟨?_, c.nreg 12 - 1, by omega, ?_⟩
      · rw [← hgv]; exact he.rv_face _ hu _ hiF
      · rw [he.tg_rv _ hu _ hiF, hqu_lt _ (by omega), hJ.cur]
  · rw [h13, hJ.cur, h12, hqu_lt _ (by omega)]
  · rw [h12] at hk
    intro i hi'
    rw [hqu_lt k (by omega)] at hi'
    exact hvis_ge _ (he.tg_lt _ (inFace_lt he (hJ.q_lt k (by omega)) hi')) (hJ.closed k hk i hi')
  · rw [h13] at h1; rw [h14] at h2
    have htn : tg d i < nf d := he.tg_lt _ (inFace_lt he hu ⟨h1, by
      have := hJ.r15; have := hJ.r14_le; omega⟩)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hvis_ge _ htn (hJ.closed_cur i h1 h2)
    · rw [hvis _ htn, hgv]; simp

theorem slot_exec (he : OEnc d W) (c : Config) (hJ : JB d W c) (hi : c.nreg 14 < c.nreg 15) :
    ∃ c' k, Exec (inp d) W slot c c' k ∧ (JB d W c' ∧ c'.nreg 12 = c.nreg 12 ∧
      c'.nreg 13 = c.nreg 13 ∧ ∀ k < c.nreg 12, qu d c' k = qu d c k) ∧
      (c'.nreg 15 - c'.nreg 14) * 18 + k + 2 ≤ (c.nreg 15 - c.nreg 14) * 18 := by
  have hs := he.size
  have hc := hJ.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hJ.regs
  have hhp := hJ.head_pos; have hhl := hJ.head_le
  have hu := hJ.q_lt _ (show c.nreg 12 - 1 < c.nreg 11 by omega)
  rw [← hJ.cur] at hu
  have hiF : InFace d (c.nreg 13) (c.nreg 14) := ⟨hJ.r14_ge, hJ.r15 ▸ hi⟩
  have hin := inFace_lt he hu hiF
  have hvn := he.tg_lt _ hin
  have htl := hJ.tail_le
  have htg : (inp d).data.getD (c.nreg 14 * c.nreg 5 + c.nreg 4) 0 = tg d (c.nreg 14) := by
    simp only [inp, tg, word, h5, h4]; congr 1; omega
  have hrv : (inp d).data.getD (c.nreg 14 * c.nreg 5 + c.nreg 4 + c.nreg 1) 0 = rv d (c.nreg 14) := by
    simp only [inp, rv, word, h5, h4, h1]; congr 1; omega
  have hvm : c.nmem (c.nreg 3 + tg d (c.nreg 14)) = vis d c (tg d (c.nreg 14)) := by rw [h3]; rfl
  have hK : ∀ c' : Config, (∀ r, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 14 → r ≠ 16 → r ≠ 17 →
      c'.nreg r = c.nreg r) → KeepsB c c' := fun c' h r a b e _ _ f _ g l => h r a b e f g l
  unfold slot
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h5]; omega
  · config_simp; rw [h5, h4]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h5, h4, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [htg, h3]; omega
  config_simp
  simp only [htg, hrv] at *
  simp only [hvm] at *
  refine spec_seq ?_
  rcases hJ.vis01 _ hvn with hv | hv
  · refine spec_ifLtN_false (by config_simp; rw [h0, hv]; omega) ?_
    exec_block
    · config_simp; rw [h6]; omega
    · config_simp; rw [h7]; omega
    · config_simp; rw [h1]; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hJ.next_enq he hi hv hw (hK _ fun r a b e f g l => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_,
      by config_simp, by config_simp, fun k hk => ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, l, ↓reduceIte]
    all_goals config_simp
    · rw [h1]
    · rw [h1]
    · funext a; simp only [upd_apply, h1, h3, h6, h7]
      try (split_ifs <;> first | omega | rfl)
    · simp only [qu, upd_apply, h3, h6, h7]
      try (split_ifs <;> first | omega | rfl)
    · rw [h1]; omega
  · refine spec_ifLtN_true (by config_simp; rw [h0, hv]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hJ.next_skip hi hv hw (hK _ fun r a b e f g l => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_,
      by config_simp, by config_simp, fun k hk => by simp only [qu]⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, f, g, l, ↓reduceIte]
    all_goals config_simp
    · rw [h1]
    · rw [h1]; omega

theorem JB.toIB {c : Config} (hJ : JB d W c) (hend : ¬ c.nreg 14 < c.nreg 15) : IB d W c := by
  refine ⟨hJ.toCB, fun k hk => ?_⟩
  rcases Nat.lt_or_ge (k + 1) (c.nreg 12) with h | h
  · exact hJ.closed k h
  · obtain rfl : k = c.nreg 12 - 1 := by omega
    rw [← hJ.cur]
    intro i hi
    exact hJ.closed_cur i hi.1 (by have := hJ.r15; have := hi.2; omega)

theorem deq_exec (he : OEnc d W) (c : Config) (hI : IB d W c) (hlt : c.nreg 12 < c.nreg 11) :
    ∃ c' k, Exec (inp d) W deq c c' k ∧ JB d W c' ∧ k = 7 ∧ c'.nreg 12 = c.nreg 12 + 1 ∧
      c'.nreg 11 = c.nreg 11 ∧ c'.nmem = c.nmem ∧
      c'.nreg 15 - c'.nreg 14 = off d (qu d c (c.nreg 12) + 1) - off d (qu d c (c.nreg 12)) := by
  have hs := he.size
  have hc := hI.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hI.regs
  have htl := hI.tail_le
  have hu := hI.q_lt _ hlt
  have hq : c.nmem (c.nreg 7 + c.nreg 12) = qu d c (c.nreg 12) := by rw [h7]; rfl
  have ho : ∀ v, (inp d).data.getD (v + c.nreg 5) 0 = off d v := fun v => by
    simp only [inp, off, word, h5]; congr 1; omega
  have ho1 : ∀ v, (inp d).data.getD (v + c.nreg 5 + c.nreg 1) 0 = off d (v + 1) := fun v => by
    simp only [inp, off, word, h5, h1]; congr 1; omega
  unfold deq
  exec_block
  · config_simp; rw [h7]; omega
  · config_simp; rw [h1]; omega
  · config_simp; rw [hq, h5]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [hq, h5, h1]; omega
  · config_simp; exact he.word_le _
  simp only [hq, ho, ho1] at *
  refine ⟨⟨⟨‹_›, oregs_of hI.regs fun r hr => ?_, by config_simp; exact hI.out,
    fun i hi => by config_simp; exact hI.bits i hi, by config_simp; rw [h1]; omega,
    by config_simp; exact hI.q_lt, by config_simp; exact hI.q_inj, by config_simp; exact hI.q0,
    by config_simp; exact hI.vis01, by config_simp; exact hI.vis_iff,
    by config_simp; exact hI.par_ok⟩, by config_simp; rw [h1]; omega, ?_, by config_simp,
    by config_simp; exact le_rfl, by config_simp; exact he.off_mono _ hu,
    fun k hk => ?_, fun i h1' h2' => by config_simp at h1'; config_simp at h2'; omega⟩,
    by first | rfl | trivial, by config_simp; rw [h1], by config_simp, by first | rfl | trivial,
    by config_simp⟩
  · config_simp
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [h1]; simp [qu]
  · config_simp at hk; rw [h1] at hk
    exact hI.closed k (by omega)

/-- The number of darts of a face. -/
def nsl (d : List ℕ) (u : ℕ) : ℕ := off d (u + 1) - off d u

theorem sum_nsl_le (he : OEnc d W) {c : Config} (hI : CB d W c) :
    ∑ k ∈ range (c.nreg 11), nsl d (qu d c k) ≤ nd d := by
  classical
  rw [← Finset.sum_image (f := nsl d) (fun k hk l hl h => hI.q_inj k (mem_range.1 hk) l
    (mem_range.1 hl) h)]
  have hsub : (range (c.nreg 11)).image (qu d c) ⊆ range (nf d) := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx; exact mem_range.2 (hI.q_lt k (mem_range.1 hk))
  refine (sum_le_sum_of_subset hsub).trans ?_
  have : ∀ k ≤ nf d, ∑ u ∈ range k, nsl d u = off d k - off d 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, ih (by omega), nsl]
      have := he.off_mono k (by omega)
      have := off_le_off he (Nat.zero_le k) (by omega : k ≤ nf d)
      omega
  rw [this _ le_rfl, he.off_last]; omega

/-- The darts of the dequeued faces. -/
def scanned (d : List ℕ) (c : Config) : ℕ := ∑ k ∈ range (c.nreg 12), nsl d (qu d c k)

/-- **The search.** -/
theorem bfs_exec (he : OEnc d W) (c : Config) (hI : IB d W c) :
    ∃ c' k, Exec (inp d) W (.whileLtN 12 11 (.seq deq (.whileLtN 14 15 slot))) c c' k ∧
      IB d W c' ∧ ¬ c'.nreg 12 < c'.nreg 11 ∧ k ≤ 11 * nf d + 18 * nd d + 2 := by
  obtain ⟨c', k, e, hI', hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 12)
    (b := 11) (body := .seq deq (.whileLtN 14 15 slot)) (IB d W)
    (fun c => 11 * (nf d - c.nreg 12) + 18 * (nd d - scanned d c)) (fun c h => h.wb)
    (fun c hc hlt => by
      obtain ⟨c₁, k₁, e₁, hJ, rfl, h12, h11, hm1, hsl⟩ := deq_exec he c hc hlt
      obtain ⟨c₂, k₂, e₂, ⟨hJ₂, h12', h13', hpre⟩, hend, hk₂⟩ := Exec.whileLtN_potential
        (P := inp d) (W := W) (a := 14) (b := 15) (body := slot)
        (fun c' => JB d W c' ∧ c'.nreg 12 = c₁.nreg 12 ∧ c'.nreg 13 = c₁.nreg 13 ∧
          ∀ k < c₁.nreg 12, qu d c' k = qu d c₁ k)
        (fun c => (c.nreg 15 - c.nreg 14) * 18) (fun c h => h.1.wb)
        (fun c' hc' hlt => by
          obtain ⟨c'', k', e', ⟨hJ', h12'', h13'', hpre'⟩, hk'⟩ := slot_exec he c' hc'.1 hlt
          exact ⟨c'', k', e', ⟨hJ', h12''.trans hc'.2.1, h13''.trans hc'.2.2.1, fun k hk =>
            (hpre' k (hc'.2.1 ▸ hk)).trans (hc'.2.2.2 k hk)⟩, hk'⟩)
        ⟨hJ, rfl, rfl, fun _ _ => rfl⟩
      refine ⟨c₂, 7 + k₂, .seq e₁ e₂, hJ₂.toIB hend, ?_⟩
      have hsc : scanned d c₂ = scanned d c + nsl d (qu d c (c.nreg 12)) := by
        unfold scanned
        rw [h12', h12, sum_range_succ]
        congr 1
        · refine sum_congr rfl fun k hk => ?_
          rw [hpre k (by rw [h12]; exact Nat.lt_succ_of_lt (mem_range.1 hk))]
          simp [qu, hm1]
        · rw [hpre _ (by omega)]; simp [qu, hm1]
      have hsle : scanned d c₂ ≤ nd d :=
        (sum_le_sum_of_subset (range_subset_range.2 hJ₂.head_le)).trans (sum_nsl_le he hJ₂.toCB)
      rw [hsc] at hsle ⊢
      rw [h12', h12]
      have := hc.head_le; have := hc.tail_le
      rw [hsl] at hk₂
      unfold nsl at hsle ⊢
      omega) hI
  refine ⟨c', k, e, hI', hn, ?_⟩
  have := Nat.sub_le (nf d) (c.nreg 12); have := Nat.sub_le (nd d) (scanned d c); omega

/-- **Every face is reached.** -/
theorem IB.all (he : OEnc d W) {c : Config} (hI : IB d W c) (hend : ¬ c.nreg 12 < c.nreg 11) :
    c.nreg 11 = nf d ∧ ∀ v < nf d, ∃ k < c.nreg 11, qu d c k = v := by
  have hcov : ∀ v < nf d, ∃ k < c.nreg 11, qu d c k = v := by
    intro v hv
    have h := he.conn v hv
    induction h with
    | refl => exact ⟨0, hI.q0.1, hI.q0.2⟩
    | tail _ harc ih =>
      obtain ⟨hu, i, hiF, rfl⟩ := harc
      obtain ⟨k, hk, hqk⟩ := ih hu
      have := hI.closed k (by have := hI.head_le; omega) i (by rw [hqk]; exact hiF)
      exact (hI.vis_iff _ hv).1 this
  refine ⟨le_antisymm hI.tail_le ?_, hcov⟩
  classical
  have h := Finset.card_le_card_of_surjOn (qu d c) (s := range (c.nreg 11)) (t := range (nf d))
    (fun v hv => by
      obtain ⟨k, hk, e⟩ := hcov v (by simpa using hv)
      exact ⟨k, by simpa using hk, e⟩)
  simpa using h

theorem bfsStart_exec (he : OEnc d W) (c : Config) (hI : I1 d W c) (h9 : c.nreg 9 = nd d) :
    ∃ c' k, Exec (inp d) W bfsStart c c' k ∧ IB d W c' ∧ k = 5 := by
  have hs := he.size
  have hc := hI.wb
  have hr := he.root_lt
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hI.regs
  unfold bfsStart
  exec_block
  · rw [h3, h8]; omega
  have hm : ∀ a, (upd (upd c.nmem (c.nreg 3 + c.nreg 8) (c.nreg 1)) (c.nreg 7) (c.nreg 8)) a =
      if a = nd d + 2 * nf d then root d else if a = nd d + root d then 1 else c.nmem a := by
    intro a; simp only [upd_apply, h1, h3, h7, h8]
  have hvis : ∀ v < nf d, (if nd d + v = nd d + 2 * nf d then root d else
      if nd d + v = nd d + root d then 1 else c.nmem (nd d + v)) = if v = root d then 1 else 0 := by
    intro v hv; split_ifs <;> first | omega | rfl | (exact hI.zero _ (by omega))
  refine ⟨⟨⟨‹_›, oregs_of hI.regs fun r hr => ?_, by config_simp; exact hI.out, fun i hi => ?_,
    by config_simp; rw [h0]; omega, fun k hk => ?_, fun k hk l hl _ => ?_, ?_, fun v hv => ?_,
    fun v hv => ?_, fun k hk1 hk2 => ?_⟩, fun k hk => ?_⟩, rfl⟩
  · config_simp
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [hm]; split_ifs <;> first | omega | exact hI.bits i (by rw [h9]; exact hi)
  · config_simp at hk; rw [h1] at hk
    obtain rfl : k = 0 := by omega
    simp only [qu]; config_simp; rw [hm]; simp; exact hr
  · config_simp at hk; config_simp at hl; omega
  · refine ⟨by config_simp; rw [h1]; omega, ?_⟩
    simp only [qu]; config_simp; rw [hm]; simp
  · simp only [vis]; config_simp; rw [hm, hvis v hv]; split_ifs <;> simp
  · simp only [vis, qu]; config_simp; simp only [hm]; simp only [hvis v hv, h1]
    constructor
    · intro h; split_ifs at h with hv'
      · exact ⟨0, by omega, by simp [hv']⟩
      all_goals simp at h
    · rintro ⟨k, hk, e⟩
      obtain rfl : k = 0 := by omega
      simp at e; simp [← e]
  · config_simp at hk2; rw [h1] at hk2; omega
  · config_simp at hk; rw [h0] at hk; omega

end phase2

/-! ### Phase 3: fixing the parent darts in reverse order -/

/-- The state of phase 3, from the end `c₀` of the search. -/
structure IR (d : List ℕ) (W : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ORegs d c
  r22_pos : 1 ≤ c.nreg 22
  r22_le : c.nreg 22 ≤ nf d
  hi : ∀ a, nd d ≤ a → c.nmem a = c₀.nmem a
  bits : ∀ i < nd d, c.nmem i ≤ 1
  anti : ∀ i < nd d, c.nmem (rv d i) = 1 - c.nmem i
  odd : ∀ j, c.nreg 22 ≤ j → j < nf d → Odd (count d c.nmem (qu d c₀ j))
  out : c.output = []

/-- The state of the count of the face `v` without its parent dart `p`. -/
structure ICn (d : List ℕ) (W : ℕ) (v p : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r ≠ 9 → r ≠ 14 → r ≠ 18 → c.nreg r = c₁.nreg r
  r14_ge : off d v ≤ c.nreg 14
  r14_le : c.nreg 14 ≤ off d (v + 1)
  mem : c.nmem = c₁.nmem
  out : c.output = c₁.output
  r18 : c.nreg 18 = ∑ i ∈ (Ico (off d v) (c.nreg 14)).filter (· ≠ p), c₁.nmem i

section phase3
variable {d : List ℕ} {W : ℕ}

theorem cnt_exec (he : OEnc d W) {v p : ℕ} {c₁ : Config} (hR : ORegs d c₁) (hv : v < nf d)
    (h15 : c₁.nreg 15 = off d (v + 1)) (h23 : c₁.nreg 23 = p)
    (hb : ∀ i < nd d, c₁.nmem i ≤ 1) (c : Config) (hI : ICn d W v p c₁ c)
    (hlt : c.nreg 14 < c.nreg 15) :
    ∃ c' k, Exec (inp d) W cnt c c' k ∧ ICn d W v p c₁ c' ∧
      (off d (v + 1) - c'.nreg 14) * 8 + k + 2 ≤ (off d (v + 1) - c.nreg 14) * 8 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := oregs_of hR fun r hr =>
    hI.regs r (by omega) (by omega) (by omega)
  have e15 : c.nreg 15 = off d (v + 1) := by
    rw [hI.regs 15 (by omega) (by omega) (by omega), h15]
  have e23 : c.nreg 23 = p := by rw [hI.regs 23 (by omega) (by omega) (by omega), h23]
  rw [e15] at hlt
  have hiS : c.nreg 14 < nd d := by
    have := off_le_off he (u := v + 1) (v := nf d) hv le_rfl
    rw [he.off_last] at this; omega
  have hge := hI.r14_ge
  have hstep : ∑ i ∈ (Ico (off d v) (c.nreg 14 + 1)).filter (· ≠ p), c₁.nmem i =
      ∑ i ∈ (Ico (off d v) (c.nreg 14)).filter (· ≠ p), c₁.nmem i +
        if c.nreg 14 ≠ p then c₁.nmem (c.nreg 14) else 0 := by
    rw [sum_filter, sum_filter, sum_Ico_succ_top hge]
  have hsum : ∑ i ∈ (Ico (off d v) (c.nreg 14)).filter (· ≠ p), c₁.nmem i ≤ nd d := by
    calc _ ≤ ∑ i ∈ (Ico (off d v) (c.nreg 14)).filter (· ≠ p), 1 :=
          sum_le_sum fun i hi => hb i (by
            have := (mem_Ico.1 (mem_filter.1 hi).1).2; omega)
      _ ≤ (Ico (off d v) (c.nreg 14)).card := by
          rw [sum_const, smul_eq_mul, mul_one]; exact card_filter_le _ _
      _ ≤ nd d := by simp; omega
  have hmi : c.nmem (c.nreg 14) = c₁.nmem (c.nreg 14) := by rw [hI.mem]
  have hb14 := hb _ hiS
  have hK : ∀ c' : Config, (∀ r, r ≠ 9 → r ≠ 14 → r ≠ 18 → c'.nreg r = c.nreg r) →
      ∀ r, r ≠ 9 → r ≠ 14 → r ≠ 18 → c'.nreg r = c₁.nreg r := fun c' h r a b e =>
    (h r a b e).trans (hI.regs r a b e)
  unfold cnt
  refine spec_seq ?_
  rcases lt_trichotomy (c.nreg 14) p with h | h | h
  · refine spec_ifLtN_true (by rw [e23]; exact h) ?_
    exec_block
    · config_simp; rw [hI.r18, hmi]; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hw, hK _ fun r a b e => ?_, by config_simp; rw [h1]; omega,
      by config_simp; rw [h1]; omega, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, ↓reduceIte]
    · config_simp; rw [h1, hstep, hI.r18, hmi]; simp [show c.nreg 14 ≠ p by omega]
    · config_simp; rw [h1]; omega
  · refine spec_ifLtN_false (by rw [e23]; omega) ?_
    refine spec_ifLtN_false (by rw [e23]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hw, hK _ fun r a b e => ?_, by config_simp; rw [h1]; omega,
      by config_simp; rw [h1]; omega, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, b, ↓reduceIte]
    · config_simp; rw [h1, hstep, hI.r18]; simp [h]
    · config_simp; rw [h1]; omega
  · refine spec_ifLtN_false (by rw [e23]; omega) ?_
    refine spec_ifLtN_true (by rw [e23]; exact h) ?_
    exec_block
    · config_simp; rw [hI.r18, hmi]; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hw, hK _ fun r a b e => ?_, by config_simp; rw [h1]; omega,
      by config_simp; rw [h1]; omega, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, ↓reduceIte]
    · config_simp; rw [h1, hstep, hI.r18, hmi]; simp [show c.nreg 14 ≠ p by omega]
    · config_simp; rw [h1]; omega

/-- **Fixing the parent dart of a face** (the mathematics of one step of phase 3). -/
theorem IR.next (he : OEnc d W) {c₀ c c' : Config} (hB : IB d W c₀) (hF : c₀.nreg 11 = nf d)
    (hI : IR d W c₀ c) (hlt : 1 < c.nreg 22) {cnt0 : ℕ}
    (hcnt : cnt0 = ∑ i ∈ (Ico (off d (qu d c₀ (c.nreg 22 - 1)))
      (off d (qu d c₀ (c.nreg 22 - 1) + 1))).filter (· ≠ par d c₀ (qu d c₀ (c.nreg 22 - 1))),
        c.nmem i)
    (hwb : WordsBounded W c') (hR : ORegs d c') (h22 : c'.nreg 22 = c.nreg 22 - 1)
    (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd c.nmem (par d c₀ (qu d c₀ (c.nreg 22 - 1))) ((cnt0 + 1) % 2))
      (rv d (par d c₀ (qu d c₀ (c.nreg 22 - 1)))) (1 - (cnt0 + 1) % 2)) :
    IR d W c₀ c' := by
  have hj : c.nreg 22 - 1 < nf d := by have := hI.r22_le; omega
  generalize hgj : c.nreg 22 - 1 = j at hcnt hmem hj
  have hj1 : 1 ≤ j := by omega
  have hv := hB.q_lt j (by rw [hF]; exact hj)
  obtain ⟨hpF, k', hk', htp⟩ := hB.par_ok j hj1 (by rw [hF]; exact hj)
  generalize hgv : qu d c₀ j = v at hv hpF htp hcnt hmem
  generalize hgp : par d c₀ v = p at hpF htp hcnt hmem
  have hpS := inFace_lt he hv hpF
  have hk'v : qu d c₀ k' ≠ v := fun e => by
    have := hB.q_inj k' (by rw [hF]; omega) j (by rw [hF]; exact hj) (e.trans hgv.symm); omega
  have htpF : tg d p < nf d := he.tg_lt _ hpS
  have hrF : InFace d (tg d p) (rv d p) := he.rv_face _ hv _ hpF
  have hrS := inFace_lt he htpF hrF
  have hrv : rv d p ∉ Ico (off d v) (off d (v + 1)) := fun h => by
    have := inFace_unique he htpF hv hrF (mem_Ico.1 h)
    exact hk'v (htp ▸ this)
  have hrp : rv d p ≠ p := fun e => hrv (by rw [e]; exact mem_Ico.2 hpF)
  set b := (cnt0 + 1) % 2 with hb
  have hb1 : b ≤ 1 := by omega
  have hm' : ∀ i, c'.nmem i = if i = rv d p then 1 - b else if i = p then b else c.nmem i := by
    intro i; rw [hmem]; simp only [upd_apply]
  -- faces processed later keep their counts
  have hfar : ∀ u < nf d, u ≠ v → u ≠ tg d p → count d c'.nmem u = count d c.nmem u := by
    intro u hu h1 h2
    refine sum_congr rfl fun i hi => ?_
    rw [hm']
    have hiF : InFace d u i := mem_Ico.1 hi
    have hne1 : i ≠ rv d p := fun e => h2 (inFace_unique he hu htpF hiF (e ▸ hrF))
    have hne2 : i ≠ p := fun e => h1 (inFace_unique he hu hv hiF (e ▸ hpF))
    simp [hne1, hne2]
  refine ⟨hwb, hR, by rw [h22]; omega, by rw [h22]; omega, fun a ha => ?_, fun i hi => ?_,
    fun i hi => ?_, fun j' hj1' hj2' => ?_, hout.trans hI.out⟩
  · rw [hm']
    rw [if_neg (by omega), if_neg (by omega)]; exact hI.hi a ha
  · rw [hm']; split_ifs <;> first | omega | exact hI.bits i hi
  · have e1 : c'.nmem p = b := by rw [hm']; simp [hrp.symm]
    have e2 : c'.nmem (rv d p) = 1 - b := by rw [hm']; simp
    by_cases h1 : i = p
    · subst h1; rw [e2, e1]
    · by_cases h2 : i = rv d p
      · subst h2; rw [he.rv_rv _ hpS, e1, e2]; omega
      · rw [hm', hm']
        have h3 : rv d i ≠ p := fun e => h2 (by rw [← e, he.rv_rv _ hi])
        have h4 : rv d i ≠ rv d p := fun e => h1 (by
          have := congrArg (rv d) e; rwa [he.rv_rv _ hi, he.rv_rv _ hpS] at this)
        simp only [h1, h2, h3, h4, ↓reduceIte]; exact hI.anti i hi
  · rw [h22, hgj] at hj1'
    rcases Nat.lt_or_ge j j' with hlt' | hle
    · have hu := hB.q_lt j' (by rw [hF]; exact hj2')
      have hne : qu d c₀ j' ≠ v := fun e => by
        have := hB.q_inj j' (by rw [hF]; exact hj2') j (by rw [hF]; exact hj) (e.trans hgv.symm)
        omega
      have hne' : qu d c₀ j' ≠ tg d p := fun e => by
        rw [htp] at e
        have := hB.q_inj j' (by rw [hF]; exact hj2') k' (by rw [hF]; omega) e
        omega
      rw [hfar _ hu hne hne']
      exact hI.odd j' (by omega) hj2'
    · obtain rfl : j' = j := by omega
      rw [hgv]
      have hpI : p ∈ Ico (off d v) (off d (v + 1)) := mem_Ico.2 hpF
      unfold count
      rw [← add_sum_erase _ _ hpI, hm']
      simp only [show p ≠ rv d p from hrp.symm, ↓reduceIte]
      have : ∑ x ∈ (Ico (off d v) (off d (v + 1))).erase p, c'.nmem x = cnt0 := by
        rw [hcnt, filter_ne']
        refine sum_congr rfl fun i hi => ?_
        rw [hm']
        have h1 : i ≠ rv d p := fun e => hrv (e ▸ (mem_erase.1 hi).2)
        simp [h1, (mem_erase.1 hi).1]
      rw [this]
      exact Nat.odd_iff.2 (by omega)

/-- The potential of phase 3. -/
def potR (d : List ℕ) (c₀ c : Config) : ℕ :=
  25 * c.nreg 22 + 8 * ∑ j ∈ range (c.nreg 22), nsl d (qu d c₀ j)

theorem fix_exec (he : OEnc d W) {c₀ : Config} (hB : IB d W c₀) (hF : c₀.nreg 11 = nf d)
    (c : Config) (hI : IR d W c₀ c) (hlt : c.nreg 1 < c.nreg 22) :
    ∃ c' k, Exec (inp d) W fix c c' k ∧ IR d W c₀ c' ∧ potR d c₀ c' + k + 2 ≤ potR d c₀ c := by
  have hs := he.size
  have hc := hI.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hI.regs
  rw [h1] at hlt
  have hj : c.nreg 22 - 1 < nf d := by have := hI.r22_le; omega
  have hv := hB.q_lt (c.nreg 22 - 1) (by rw [hF]; exact hj)
  obtain ⟨hpF, k', hk', htp⟩ := hB.par_ok (c.nreg 22 - 1) (by omega) (by rw [hF]; exact hj)
  have hpS := inFace_lt he hv hpF
  have hqm : c.nmem (c.nreg 7 + (c.nreg 22 - c.nreg 1)) = qu d c₀ (c.nreg 22 - 1) := by
    rw [h7, h1, hI.hi _ (by omega)]; rfl
  have hpm : c.nmem (c.nreg 6 + qu d c₀ (c.nreg 22 - 1)) = par d c₀ (qu d c₀ (c.nreg 22 - 1)) := by
    rw [h6, hI.hi _ (by omega)]; rfl
  have ho : ∀ v, (inp d).data.getD (v + c.nreg 5) 0 = off d v := fun v => by
    simp only [inp, off, word, h5]; congr 1; omega
  have ho1 : ∀ v, (inp d).data.getD (v + c.nreg 5 + c.nreg 1) 0 = off d (v + 1) := fun v => by
    simp only [inp, off, word, h5, h1]; congr 1; omega
  generalize hgv : qu d c₀ (c.nreg 22 - 1) = v at hv hpF htp hpS hqm hpm
  generalize hgp : par d c₀ v = p at hpF htp hpS hpm
  -- the head of the step
  have eA : ∃ c₁ k₁, Exec (inp d) W (block [.subN 22 22 1, .addN 10 7 22, .loadN 16 10,
      .addN 10 6 16, .loadN 23 10, .addN 10 16 5, .readIn 14 10, .addN 10 10 1, .readIn 15 10,
      .copyN 18 0]) c c₁ k₁ ∧ WordsBounded W c₁ ∧ k₁ = 10 ∧ c₁.nreg 22 = c.nreg 22 - 1 ∧
      c₁.nreg 23 = p ∧ c₁.nreg 14 = off d v ∧ c₁.nreg 15 = off d (v + 1) ∧ c₁.nreg 18 = 0 ∧
      (∀ r, r ≠ 10 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 18 → r ≠ 22 → r ≠ 23 →
        c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    exec_block
    any_goals first
      | exact he.word_le _
      | (config_simp; (try rw [hqm]); (try rw [hpm]); (try rw [h7]); (try rw [h6]);
          (try rw [h5]); (try rw [h1]); omega)
    refine ⟨‹_›, rfl, by config_simp; rw [h1], by config_simp; rw [hqm, hpm],
      by config_simp; rw [hqm, ho], by config_simp; rw [hqm, ho1], by config_simp; exact h0,
      fun r a b e f g l m => ?_, rfl, rfl⟩
    config_simp; simp only [upd_apply, a, b, e, f, g, l, m, ↓reduceIte]
  obtain ⟨c₁, k₁, eA, hw₁, rfl, h22₁, h23₁, h14₁, h15₁, h18₁, hr₁, hm₁, ho₁⟩ := eA
  have hR₁ : ORegs d c₁ := oregs_of hI.regs fun r hr => hr₁ r (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hb₁ : ∀ i < nd d, c₁.nmem i ≤ 1 := fun i hi => by rw [hm₁]; exact hI.bits i hi
  have hC₁ : ICn d W v p c₁ c₁ := ⟨hw₁, fun _ _ _ _ => rfl, by rw [h14₁],
    by rw [h14₁]; exact he.off_mono v hv, rfl, rfl, by rw [h18₁, h14₁]; simp⟩
  obtain ⟨c₂, k₂, eB, hC₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 14)
    (b := 15) (body := cnt) (ICn d W v p c₁) (fun c => (off d (v + 1) - c.nreg 14) * 8)
    (fun c h => h.wb) (fun c' hc' hlt' => cnt_exec he hR₁ hv h15₁ h23₁ hb₁ c' hc' hlt') hC₁
  have h14₂ : c₂.nreg 14 = off d (v + 1) := by
    have := hC₂.r14_le
    rw [hC₂.regs 15 (by omega) (by omega) (by omega), h15₁] at hn₂; omega
  have hR₂ : ORegs d c₂ := oregs_of hR₁ fun r hr => hC₂.regs r (by omega) (by omega) (by omega)
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g20⟩ := hR₂
  have e23 : c₂.nreg 23 = p := by rw [hC₂.regs 23 (by omega) (by omega) (by omega), h23₁]
  have hcnt := hC₂.r18
  rw [h14₂, hm₁] at hcnt
  have hcle : c₂.nreg 18 ≤ nd d := by
    rw [hcnt]
    calc _ ≤ ∑ i ∈ (Ico (off d v) (off d (v + 1))).filter (· ≠ p), 1 :=
          sum_le_sum fun i hi => hI.bits i (inFace_lt he hv (mem_Ico.1 (mem_filter.1 hi).1))
      _ ≤ (Ico (off d v) (off d (v + 1))).card := by
          rw [sum_const, smul_eq_mul, mul_one]; exact card_filter_le _ _
      _ ≤ nd d := by
          simp only [Nat.card_Ico]
          have := off_le_off he (u := v + 1) (v := nf d) hv le_rfl
          rw [he.off_last] at this; omega
  have hrvw : (inp d).data.getD (c₂.nreg 23 * c₂.nreg 5 + c₂.nreg 4 + c₂.nreg 1) 0 = rv d p := by
    simp only [inp, rv, word, e23, g5, g4, g1]; congr 1; omega
  have hrvw' : (inp d).data.getD (p * c₂.nreg 5 + c₂.nreg 4 + 1) 0 = rv d p := by
    simp only [inp, rv, word, g5, g4]; congr 1; omega
  have hw₂ := hC₂.wb
  -- the tail of the step
  have eC : ∃ c₃ k₃, Exec (inp d) W (block [.addN 18 18 1, .modN 18 18 20, .storeN 23 18,
      .mulN 10 23 5, .addN 10 10 4, .addN 10 10 1, .readIn 17 10, .subN 9 1 18, .storeN 17 9])
      c₂ c₃ k₃ ∧ IR d W c₀ c₃ ∧ c₃.nreg 22 = c.nreg 22 - 1 ∧ k₃ = 9 := by
    clear eA eB
    exec_block
    · config_simp; rw [g1]; omega
    · config_simp; rw [e23, g5]; omega
    · config_simp; rw [e23, g5, g4]; omega
    · config_simp; rw [e23, g5, g4, g1]; omega
    · config_simp; exact he.word_le _
    refine ⟨IR.next he hB hF hI (by omega) (cnt0 := c₂.nreg 18) ?_ ‹_› (oregs_of ⟨g0, g1, g2, g3,
      g4, g5, g6, g7, g8, g20⟩ fun r hr => ?_) ?_ ?_ ?_, ?_, rfl⟩
    · rw [hcnt, hgv, hgp]
    · config_simp
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · config_simp; rw [hC₂.regs 22 (by omega) (by omega) (by omega), h22₁]
    · config_simp; rw [hC₂.out, ho₁]
    · config_simp
      simp only [g1, g20, e23, hC₂.mem, hm₁, hgv, hgp, hrvw']
    · config_simp; rw [hC₂.regs 22 (by omega) (by omega) (by omega), h22₁]
  obtain ⟨c₃, k₃, eC, hI₃, h22₃, rfl⟩ := eC
  refine ⟨c₃, _, .seq eA (.seq eB eC), hI₃, ?_⟩
  unfold potR
  rw [h22₃]
  obtain ⟨r, hr⟩ : ∃ r, c.nreg 22 = r + 1 := ⟨c.nreg 22 - 1, by omega⟩
  have hqr : qu d c₀ r = v := by rw [← hgv, hr, Nat.add_sub_cancel]
  rw [hr, Nat.add_sub_cancel, sum_range_succ, hqr]
  rw [h14₁] at hk₂
  unfold nsl
  omega

/-- **Phase 3**: the parent darts are fixed in reverse order of the search. -/
theorem fixAll_exec (he : OEnc d W) {c₀ : Config} (hB : IB d W c₀)
    (hend : ¬ c₀.nreg 12 < c₀.nreg 11) :
    ∃ c₁ c' k, Exec (inp d) W (.instr (.copyN 22 11)) c₀ c₁ 1 ∧
      Exec (inp d) W (.whileLtN 1 22 fix) c₁ c' k ∧ IR d W c₀ c' ∧ c'.nreg 22 = 1 ∧
      k ≤ 25 * nf d + 8 * nd d + 2 := by
  obtain ⟨hF, -⟩ := IB.all he hB hend
  have hw := hB.wb
  have hr := he.root_lt
  have e₁ := Exec.copyN (P := inp d) hw 22 11
  have hI : IR d W c₀ { c₀ with nreg := upd c₀.nreg 22 (c₀.nreg 11) } := by
    refine ⟨e₁.wb_right, oregs_of hB.regs fun r hr => ?_, by config_simp; omega,
      by config_simp; omega, fun a _ => rfl, fun i hi => ?_, fun i hi => ?_,
      fun j hj hj' => ?_, hB.out⟩
    · config_simp
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rw [hB.bits i hi]; exact he.ini_le i hi
    · rw [hB.bits i hi, hB.bits _ (he.rv_lt i hi)]; exact he.ini_rv i hi
    · config_simp at hj; omega
  obtain ⟨c', k, e, hI', hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 1)
    (b := 22) (body := fix) (IR d W c₀) (potR d c₀) (fun c h => h.wb)
    (fun c hc hlt => fix_exec he hB hF c hc hlt) hI
  refine ⟨_, c', k, e₁, e, hI', ?_, ?_⟩
  · have := hI'.r22_pos; rw [hI'.regs.2.1] at hn; omega
  · have hs := sum_nsl_le he hB.toCB
    unfold potR at hk
    simp only [upd_apply, ↓reduceIte] at hk
    rw [hF] at hs hk
    omega

/-- The bits at the end of phase 3 form an orientation with odd counts. -/
theorem IR.isOrient {c₀ c : Config} (hB : IB d W c₀) (hF : c₀.nreg 11 = nf d)
    (hall : ∀ v < nf d, ∃ k < c₀.nreg 11, qu d c₀ k = v) (hI : IR d W c₀ c)
    (h22 : c.nreg 22 = 1) : IsOrient d c.nmem := by
  refine ⟨hI.bits, hI.anti, fun u hu hne => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hall u hu
  have hk0 : k ≠ 0 := fun e => hne (by rw [e]; exact hB.q0.2)
  exact hI.odd k (by omega) (by omega)

end phase3

/-! ### Phase 4: the output -/

/-- The state of the output phase. -/
structure IO (d : List ℕ) (W : ℕ) (o : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : ORegs d c
  r9 : c.nreg 9 ≤ nd d
  mem : c.nmem = o
  out : c.output = (List.range (c.nreg 9)).map o

section phase4
variable {d : List ℕ} {W : ℕ}

theorem outStep_exec (he : OEnc d W) {o : ℕ → ℕ} (c : Config) (hI : IO d W o c)
    (hlt : c.nreg 9 < c.nreg 3) :
    ∃ c' k, Exec (inp d) W outStep c c' k ∧ IO d W o c' ∧
      (nd d - c'.nreg 9) * 5 + k + 2 ≤ (nd d - c.nreg 9) * 5 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h20⟩ := hI.regs
  rw [h3] at hlt
  unfold outStep
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, oregs_of hI.regs fun r hr => ?_, by config_simp; rw [h1]; omega,
    by config_simp; exact hI.mem, ?_⟩, by config_simp; rw [h1]; omega⟩
  · config_simp
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; rw [h1, hI.out, List.range_succ, List.map_append, hI.mem]; simp

end phase4

/-! ### The whole program -/

section main
variable {d : List ℕ} {W : ℕ}

theorem orient_exec (he : OEnc d W) :
    ∃ o c' k, Exec (inp d) W orient initConfig c' k ∧ IsOrient d o ∧
      c'.output = (List.range (nd d)).map o ∧ k ≤ 36 * nf d + 39 * nd d + 26 := by
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ := setup_exec he
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 9)
    (b := 3) (body := iniStep) (I1 d W) (fun c => (nd d - c.nreg 9) * 8) (fun c h => h.wb)
    (fun c hc hlt => iniStep_exec he c hc hlt) hI₁
  have h9₂ : c₂.nreg 9 = nd d := by
    have := hI₂.r9; rw [hI₂.regs.2.2.2.1] at hn₂; omega
  obtain ⟨c₃, k₃, e₃, hB₃, rfl⟩ := bfsStart_exec he c₂ hI₂ h9₂
  obtain ⟨c₄, k₄, e₄, hB₄, hn₄, hk₄⟩ := bfs_exec he c₃ hB₃
  obtain ⟨hF, hall⟩ := IB.all he hB₄ hn₄
  obtain ⟨c₅, c₆, k₆, e₅, e₆, hR₆, h22₆, hk₆⟩ := fixAll_exec he hB₄ hn₄
  have hO := IR.isOrient hB₄ hF hall hR₆ h22₆
  have hw₆ := hR₆.wb
  have e₇ := Exec.copyN (P := inp d) hw₆ 9 0
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g20⟩ := hR₆.regs
  have hIO : IO d W c₆.nmem { c₆ with nreg := upd c₆.nreg 9 (c₆.nreg 0) } := by
    refine ⟨e₇.wb_right, oregs_of hR₆.regs fun r hr => ?_, by config_simp; omega, rfl, ?_⟩
    · config_simp
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · config_simp; rw [hR₆.out, g0]; rfl
  obtain ⟨c₈, k₈, e₈, hO₈, hn₈, hk₈⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 9)
    (b := 3) (body := outStep) (IO d W c₆.nmem) (fun c => (nd d - c.nreg 9) * 5)
    (fun c h => h.wb) (fun c hc hlt => outStep_exec he c hc hlt) hIO
  have h9₈ : c₈.nreg 9 = nd d := by
    have := hO₈.r9; rw [hO₈.regs.2.2.2.1] at hn₈; omega
  refine ⟨c₆.nmem, c₈, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆
    (.seq e₇ e₈)))))), hO, by rw [hO₈.out, h9₈], ?_⟩
  beta_reduce at hk₂ hk₈
  have a1 := Nat.sub_le (nd d) (c₁.nreg 9)
  have a2 := Nat.sub_le (nd d) (({ c₆ with nreg := upd c₆.nreg 9 (c₆.nreg 0) } : Config).nreg 9)
  omega

/-- **The Kasteleyn orientation on the machine.** On a well-formed input with `F` faces and
`S` darts, the program halts within `36 F + 39 S + 27` steps and prints, for every dart, a bit:
the bits of a dart and of its reverse are complementary, and every face other than the root
carries an odd number of `1` bits. -/
theorem orient_runsWithin (he : OEnc d W) :
    ∃ o, IsOrient d o ∧ RunsWithin (compile orient 0 ++ [Instr.halt]) (inp d) W
      (36 * nf d + 39 * nd d + 27) ((List.range (nd d)).map o) := by
  obtain ⟨o, c', k, e, hO, hout, hk⟩ := orient_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨o, hO, k', by omega, h1, h2⟩

end main

end Orient

end Kasteleyn
