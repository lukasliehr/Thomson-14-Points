module

public import CAP.PSD.Sound
public import N14.Energy.Kernel

/-!
# T7, the blocks of a certificate are positive definite

`blk_posDef`: a block whose matrix the checker of `CAP.PSD` accepts, with the slot width and the bias of the
identity, has a positive definite matrix (`CAP.PSD.check_sound`; the matrix of that statement is the matrix
`symMat` of the kernels). `blkPD_nil`, `blkPD_cons`, `blkPD_cons'` assemble the statement for a list of blocks:
what the kernels need is that the quadratic form of every block is nonnegative (`QuadNN`).
-/

@[expose] public section

namespace N14.Energy

open CAP CAP.ThreePoint N14.Ident

/-- The matrix of the statement of `CAP.PSD` is the matrix of the block of the kernel. -/
theorem blk_posDef (P : ThreePoint.Params) (Pp : CAP.PSD.Params) (B : Blk) (cols : ℕ) (hn : Pp.n = B.N)
    (hw : Pp.w = P.w) (ha : Pp.a = P.a) (h : CAP.PSD.check Pp B.rows cols = true) :
    (symMat P B.N B.rows).PosDef := by
  have h1 := CAP.PSD.check_sound Pp B.rows cols h
  have e : ∀ (n : ℕ) (hn' : Pp.n = n), (symMat P n B.rows).PosDef := by
    intro n hn'
    subst hn'
    have e : (CAP.PSD.gram Pp B.rows).map (Int.cast : ℤ → ℝ) = symMat P Pp.n B.rows := by
      ext i j
      show ((CAP.PSD.gram Pp B.rows i j : ℤ) : ℝ) = symEnt P Pp.n B.rows i j
      unfold CAP.PSD.gram symEnt CAP.PSD.dataEntry entZ
      rw [hw, ha]
      rcases lt_trichotomy i j with h | h | h
      · have h' : (i : ℕ) < j := h
        rw [if_neg h.ne, if_pos h, if_neg h'.ne, if_pos h']
      · subst h
        rw [if_pos rfl, if_pos rfl, Nat.sub_self, Int.cast_mul, Int.cast_ofNat]
      · have h' : (j : ℕ) < i := h
        rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_neg h'.ne', if_neg (not_lt.mpr h'.le)]
    rw [e] at h1
    exact h1
  exact e B.N hn

theorem blkPD_nil (P : ThreePoint.Params) : BlkPD P [] := fun _ h => absurd h List.not_mem_nil

/-- A block with a nonnegative quadratic form in front of a list. -/
theorem blkPD_cons' {P : ThreePoint.Params} {B : Blk} {l : List Blk} (h : QuadNN P B.N B.rows)
    (hl : BlkPD P l) : BlkPD P (B :: l) := by
  intro B' hB'
  rcases List.mem_cons.mp hB' with rfl | hm
  · exact h
  · exact hl B' hm

/-- A block with a positive definite matrix in front of a list. -/
theorem blkPD_cons {P : ThreePoint.Params} {B : Blk} {l : List Blk} (h : (symMat P B.N B.rows).PosDef)
    (hl : BlkPD P l) : BlkPD P (B :: l) :=
  blkPD_cons' (quad_nonneg P B.N B.rows h) hl

end N14.Energy
