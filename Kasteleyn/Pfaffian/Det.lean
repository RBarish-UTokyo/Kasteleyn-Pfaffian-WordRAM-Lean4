module

public import Kasteleyn.Pfaffian.Minor

/-!
# The square of the Pfaffian is the determinant

We prove Cayley's theorem: for an alternating matrix `A` (zero diagonal and `A j i = -A i j`)
over a commutative ring, `pf A ^ 2 = det A`.

The proof is by induction on the size, together with the companion identity for odd sets: if
`#s` is odd and `i, j ∈ s`, then the minor of `A` with rows `s \ {i}` and columns `s \ {j}` is
`pfOn A (s \ {i}) * pfOn A (s \ {j})`. In other words, the adjugate of an alternating matrix of
odd size is the rank-one matrix `w wᵀ` with `w i = (-1) ^ i * Pf (A without row and column i)`.
Both identities are proved by Laplace expansion of the determinant, using the expansion of the
Pfaffian along an arbitrary row.

## Main results

* `Kasteleyn.pfOn_sq`: `pfOn A s ^ 2 = minor A s s` for every finite set `s`.
* `Kasteleyn.minor_erase_erase`: `minor A (s \ {i}) (s \ {j}) = pfOn A (s \ {i}) * pfOn A (s \ {j})`
  for `#s` odd.
* `Kasteleyn.pf_sq`: `pf A ^ 2 = A.det`.

## References

* A. Cayley, *Sur les déterminants gauches*, J. reine angew. Math. 38 (1849), 93–96.
-/

@[expose] public section

namespace Kasteleyn

open Finset Matrix

variable {ι : Type*} [LinearOrder ι] {R : Type*} [CommRing R]

lemma rankIn_eq_zero_of_le {t : Finset ι} {a : ι} (h : ∀ x ∈ t, a ≤ x) : rankIn t a = 0 := by
  unfold rankIn
  rw [card_eq_zero, filter_eq_empty_iff]
  exact fun x hx => not_lt.2 (h x hx)

variable {A : Matrix ι ι R}

/-- The two identities `Pf² = det` (for every set) and `adj = w wᵀ` (for odd sets), proved
together by strong induction on the cardinality. -/
theorem pfOn_sq_and_minor_erase_erase (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j)
    (n : ℕ) :
    (∀ s : Finset ι, #s = n → pfOn A s ^ 2 = minor A s s) ∧
    (∀ s : Finset ι, #s = n → Odd n → ∀ i ∈ s, ∀ j ∈ s,
      minor A (s.erase i) (s.erase j) = pfOn A (s.erase i) * pfOn A (s.erase j)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  refine ⟨fun s hs => ?_, fun s hs hn i hi j hj => ?_⟩
  · -- `Pf² = det`
    rcases Nat.even_or_odd n with he | ho
    swap
    · rw [pfOn_eq_zero_of_odd A (hs ▸ ho), minor_self_eq_zero_of_odd hd hA (hs ▸ ho)]
      ring
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    have hpos : 0 < n := hs ▸ card_pos.2 hne
    obtain ⟨a, ha_def⟩ : ∃ a, s.min' hne = a := ⟨_, rfl⟩
    have ha : a ∈ s := ha_def ▸ min'_mem s hne
    have hra : rankIn s a = 0 := ha_def ▸ rankIn_min' hne
    have hTc : #(s.erase a) = n - 1 := by rw [card_erase_of_mem ha, hs]
    have hTo : Odd (n - 1) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨k - 1, by omega⟩
    have hQ := (ih (n - 1) (by omega)).2 (s.erase a) hTc hTo
    rw [minor_expand_row A rfl ha, ← add_sum_erase s _ ha, hd a, mul_zero, zero_mul, zero_add,
      pfOn_eq_sum_min A hne, ha_def, sq, sum_mul_sum]
    refine sum_congr rfl fun b hb => ?_
    have hab : a < b := ha_def ▸ min'_lt_of_mem_erase_min' s hne (ha_def ▸ hb)
    have has : a ∈ s.erase b := mem_erase.2 ⟨hab.ne, ha⟩
    rw [minor_expand_col A (by rw [card_erase_of_mem ha, card_erase_of_mem (mem_of_mem_erase hb)])
      has, mul_sum]
    refine sum_congr rfl fun c hc => ?_
    have hac : a < c := ha_def ▸ min'_lt_of_mem_erase_min' s hne (ha_def ▸ hc)
    have h1 := rankIn_erase ha c
    rw [ltInd_of_lt hac] at h1
    have h2 : rankIn (s.erase b) a = 0 :=
      rankIn_eq_zero_of_le fun x hx => ha_def ▸ min'_le s x (mem_of_mem_erase hx)
    rw [show (s.erase b).erase a = (s.erase a).erase b from erase_right_comm, hQ c hc b hb,
      hA a c, hra, h2, h1]
    ring
  · -- the adjugate identity for odd sets
    rcases eq_or_ne i j with rfl | hij
    · rw [← sq]
      have hpos : 0 < n := hs ▸ card_pos.2 ⟨i, hi⟩
      exact ((ih (n - 1) (by omega)).1 (s.erase i) (by rw [card_erase_of_mem hi, hs])).symm
    have hjs : j ∈ s.erase i := mem_erase.2 ⟨hij.symm, hj⟩
    have his : i ∈ s.erase j := mem_erase.2 ⟨hij, hi⟩
    have hSc : #((s.erase i).erase j) = n - 2 := by
      rw [card_erase_of_mem hjs, card_erase_of_mem hi, hs]
      omega
    have hn2 : 2 ≤ n := by
      have := card_le_card (show {i, j} ⊆ s by simp [insert_subset_iff, hi, hj])
      rw [card_pair hij] at this
      omega
    have hSo : Odd (n - 2) := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k - 1, by omega⟩
    have hQ := (ih (n - 2) (by omega)).2 ((s.erase i).erase j) hSc hSo
    have hcard : #(s.erase i) = #(s.erase j) := by
      rw [card_erase_of_mem hi, card_erase_of_mem hj]
    rw [minor_expand_row A hcard hjs, ← add_sum_erase _ _ his,
      show (s.erase j).erase i = (s.erase i).erase j from erase_right_comm,
      minor_self_eq_zero_of_odd hd hA (hSc ▸ hSo), mul_zero, zero_add,
      pfOn_expand hA hjs, pfOn_expand hA his,
      show (s.erase j).erase i = (s.erase i).erase j from erase_right_comm, sum_mul_sum]
    refine sum_congr rfl fun c hc => ?_
    obtain ⟨hcj, hci, hcs⟩ : c ≠ j ∧ c ≠ i ∧ c ∈ s := by simpa using hc
    have hic : i ∈ (s.erase j).erase c := mem_erase.2 ⟨hci.symm, his⟩
    have hcard' : #((s.erase i).erase j) = #((s.erase j).erase c) := by
      rw [card_erase_of_mem hjs, card_erase_of_mem hi,
        card_erase_of_mem (mem_erase.2 ⟨hcj, hcs⟩), card_erase_of_mem hj]
    rw [minor_expand_col A hcard' hic, mul_sum]
    refine sum_congr rfl fun b hb => ?_
    rw [show ((s.erase j).erase c).erase i = ((s.erase i).erase j).erase c by
        ext x; simp only [mem_erase]; tauto,
      hQ b hb c hc, hA i b]
    obtain ⟨hbj, hbi, hbs⟩ : b ≠ j ∧ b ≠ i ∧ b ∈ s := by simpa using hb
    -- the sign identity
    have h2 := rankIn_erase hj c
    have h3 := rankIn_erase hi c
    have h4 := rankIn_erase hjs b
    have h5 := rankIn_erase hi b
    have h6 := rankIn_erase hj b
    have h7 := rankIn_erase (mem_erase.2 ⟨hcj, hcs⟩) i
    have e1 := ltInd_add_ltInd hci
    have hsign : (-1 : R) ^ (rankIn (s.erase i) j + rankIn (s.erase j) c) *
        (-1) ^ (rankIn ((s.erase i).erase j) b + rankIn ((s.erase j).erase c) i) * (-1) =
        pairSign (s.erase i) j c * pairSign (s.erase j) i b := by
      unfold pairSign
      rw [← pow_add, ← pow_add, ← pow_succ]
      apply neg_one_pow_eq_of_mod_two
      omega
    calc (-1 : R) ^ (rankIn (s.erase i) j + rankIn (s.erase j) c) * A j c *
          ((-1) ^ (rankIn ((s.erase i).erase j) b + rankIn ((s.erase j).erase c) i) * -A i b *
            (pfOn A (((s.erase i).erase j).erase b) * pfOn A (((s.erase i).erase j).erase c)))
        = ((-1 : R) ^ (rankIn (s.erase i) j + rankIn (s.erase j) c) *
            (-1) ^ (rankIn ((s.erase i).erase j) b + rankIn ((s.erase j).erase c) i) * (-1)) *
            A j c * A i b *
            (pfOn A (((s.erase i).erase j).erase b) * pfOn A (((s.erase i).erase j).erase c)) := by
          ring
      _ = _ := by rw [hsign]; ring

/-- **Cayley's theorem** for principal submatrices: `pfOn A s ^ 2 = minor A s s`. -/
theorem pfOn_sq (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j) (s : Finset ι) :
    pfOn A s ^ 2 = minor A s s :=
  (pfOn_sq_and_minor_erase_erase hd hA #s).1 s rfl

/-- The adjugate of an alternating matrix of odd size has rank one: if `#s` is odd and
`i, j ∈ s`, the minor with rows `s \ {i}` and columns `s \ {j}` is the product of the Pfaffians
of `s \ {i}` and `s \ {j}`. -/
theorem minor_erase_erase (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j) {s : Finset ι}
    (hs : Odd #s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    minor A (s.erase i) (s.erase j) = pfOn A (s.erase i) * pfOn A (s.erase j) :=
  (pfOn_sq_and_minor_erase_erase hd hA #s).2 s rfl hs i hi j hj

/-- **Cayley's theorem**: the square of the Pfaffian of an alternating matrix is its
determinant. This holds over any commutative ring. -/
theorem pf_sq [Fintype ι] (hd : ∀ i, A i i = 0) (hA : ∀ i j, A j i = -A i j) :
    pf A ^ 2 = A.det := by
  rw [pf_def, pfOn_sq hd hA, minor_univ]

/-- **Cayley's theorem**, stated with the transpose: if `Aᵀ = -A` and `A` has zero diagonal,
then `pf A ^ 2 = det A`. -/
theorem pf_sq_of_transpose_eq_neg [Fintype ι] (hd : ∀ i, A i i = 0) (hA : Aᵀ = -A) :
    pf A ^ 2 = A.det :=
  pf_sq hd fun i j => by simpa using congrFun (congrFun hA i) j

end Kasteleyn
