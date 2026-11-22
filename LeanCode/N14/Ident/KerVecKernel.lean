module

public import N14.Ident.Kernel

/-!
# T7, a block with a kernel vector: the checker (`Init` only)

In the certificate of the cap 13 of the 22 matrices `F` are singular: the source gives `F = N G Nᵀ` with a
matrix `N` that has one column less than rows. Such a matrix is positive semidefinite, and it has a kernel
vector `v`. This checker verifies a kernel vector of the symmetric matrix `S` of a block (`S k k = 2 X k k`,
`S k j = X (min k j) (max k j)` otherwise, with the stored upper triangle `X`):

* `S v = 0`, for the vector `v j = slot wv Vp j - slot wv Vn j`;
* `v i ≠ 0` for an index `i < n`;
* the number of the block has no bits beyond its slots, and the slot of the diagonal entry `i` has room for `c`.

Together with the positive definiteness of the block in which `c` is added to the stored diagonal entry `i`
(the checker of `CAP.PSD`), this gives that the quadratic form of the block is nonnegative
(`N14.Energy.quadNN_of_kernel`).

The checker is bit-exact with `ker_vec_ok` of `N14/py/identref.py`.
-/

@[expose] public section

namespace N14.Ident

open CAP CAP.ThreePoint

/-- The stored entry that the symmetric matrix of a block has at `(k, j)`: slot `|k - j|` of row `min k j`. -/
noncomputable def kvEnt (P : Params) (n rows k j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (slot P.w rows (Nat.add (triOffK n j) (Nat.sub k j)))
    (slot P.w rows (Nat.add (triOffK n k) (Nat.sub j k)))
    (Nat.ble k j)

/-- The factor of the stored entry: `2` on the diagonal, `1` elsewhere. -/
noncomputable def kvMul (k j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 1 2 (Nat.beq k j)

/-- The two parts of `∑_{j < cnt} S k j * v j`. -/
noncomputable def kvRow (P : Params) (n rows wv Vp Vn k : Nat) : Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun j ih =>
      (Nat.add ih.1 (Nat.mul (kvMul k j)
          (Nat.add (Nat.mul (kvEnt P n rows k j) (slot wv Vp j))
            (Nat.mul (Nat.shiftLeft 1 (Nat.sub P.a 1)) (slot wv Vn j)))),
       Nat.add ih.2 (Nat.mul (kvMul k j)
          (Nat.add (Nat.mul (kvEnt P n rows k j) (slot wv Vn j))
            (Nat.mul (Nat.shiftLeft 1 (Nat.sub P.a 1)) (slot wv Vp j))))))

/-- The rows `k < cnt` of `S v` vanish. -/
noncomputable def kvAll (P : Params) (n rows wv Vp Vn : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => ih && Nat.beq (kvRow P n rows wv Vp Vn k n).1 (kvRow P n rows wv Vp Vn k n).2)

/-- The checker of a kernel vector of a block of order `n`. -/
noncomputable def kerVecOk (P : Params) (n rows wv Vp Vn i c : Nat) : Bool :=
  kvAll P n rows wv Vp Vn n && Nat.blt i n && !(Nat.beq (slot wv Vp i) (slot wv Vn i)) &&
    Nat.blt rows (Nat.shiftLeft 1 (Nat.mul P.w (triOffK n n))) &&
    Nat.blt (Nat.add (slot P.w rows (triOffK n i)) c) (Nat.shiftLeft 1 P.w)

end N14.Ident
