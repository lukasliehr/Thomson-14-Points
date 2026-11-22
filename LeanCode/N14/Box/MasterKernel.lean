module

public import N14.Box.Kernel

/-!
# T7, the slack on a domain: groups that cover arbitrary boxes, and the master tree (`Init` only)

**Why.** The kernel keeps what an evaluation computes, so the memory of a module is that of its largest
evaluation. A group of `N14.Box.groupOk` is a range of boxes of a grid, hence at least one box of the grid, and a
box of the grid with many cells or with a large tree is one large evaluation. Here a group is the cover of an
arbitrary box whose sides are dyadic intervals (`boxOk`), so its size is a choice of the certificate.

**The master tree** (`masterOk`). The statement module contains the list of the boxes of all groups and a tree
that the kernel verifies in one evaluation: for every box of the grid of the level `lv`, a tree of bisections
whose leaves either violate a cut at all of their points (the test `boxOut` of the cover) or are the next box of
the list. The tree has the format of the cover: two bits for a node, `0`, `1`, `2` for a bisection in this
coordinate, `3` for a leaf. Its evaluation compares small numbers only.

The checker is bit-exact with `N14/py/boxref.py` (`box_ok`, `master`, `master_ok`).
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein

/-- A box whose sides are the intervals `(e₁, c₁)`, `(e₂, c₂)`, `(e₃, c₃)`: in the coordinate `a` it is
`[c_a / 2 ^ e_a - 1, (c_a + 1) / 2 ^ e_a - 1]`. -/
structure Bx where
  e1 : Nat
  c1 : Nat
  e2 : Nat
  c2 : Nat
  e3 : Nat
  c3 : Nat

/-- The list is empty. -/
noncomputable def isNil {α : Type} : List α → Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false)

/-- The checker of a group: the box `b` is covered by the cells of the list (`cover`), and all of them are
used. `s` is the number of the tree of the cover. -/
noncomputable def boxOk (R : Run) (b : Bx) (s : Nat) (cells : List Cell) : Bool :=
  cover R R.fuel s b.e1 b.c1 b.e2 b.c2 b.e3 b.c3 cells (fun _ l => isNil l)

/-- The box `b` has the intervals `(e₁, c₁)`, `(e₂, c₂)`, `(e₃, c₃)`. -/
noncomputable def bxIs (b : Bx) (e1 c1 e2 c2 e3 c3 : Nat) : Bool :=
  Nat.beq b.e1 e1 && Nat.beq b.c1 c1 && Nat.beq b.e2 e2 && Nat.beq b.c2 c2 && Nat.beq b.e3 e3 && Nat.beq b.c3 c3

/-- The checker of the master tree of a box: the tree of `cover` with the boxes of the list in the place of the
cells. At a leaf the box violates a cut at all of its points, or it is the next box of the list. `k` tests the
rest of the number and of the list after the tree. The first argument bounds the depth. -/
noncomputable def master (R : Run) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Bx → (Nat → List Bx → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Bx → (Nat → List Bx → Bool) → Bool)
    (fun _ _ _ _ _ _ _ _ _ => false)
    (fun _ ih s e1 c1 e2 c2 e3 c3 l k =>
      Nat.rec (motive := fun _ => Bool)
        (ih (Nat.shiftRight s 2) (Nat.succ e1) (Nat.mul 2 c1) e2 c2 e3 c3 l
          (fun s' l' => ih s' (Nat.succ e1) (Nat.succ (Nat.mul 2 c1)) e2 c2 e3 c3 l' k))
        (fun t _ => Nat.rec (motive := fun _ => Bool)
          (ih (Nat.shiftRight s 2) e1 c1 (Nat.succ e2) (Nat.mul 2 c2) e3 c3 l
            (fun s' l' => ih s' e1 c1 (Nat.succ e2) (Nat.succ (Nat.mul 2 c2)) e3 c3 l' k))
          (fun t' _ => Nat.rec (motive := fun _ => Bool)
            (ih (Nat.shiftRight s 2) e1 c1 e2 c2 (Nat.succ e3) (Nat.mul 2 c3) l
              (fun s' l' => ih s' e1 c1 e2 c2 (Nat.succ e3) (Nat.succ (Nat.mul 2 c3)) l' k))
            (fun _ _ =>
              Bool.rec (motive := fun _ => Bool)
                (List.rec (motive := fun _ => Bool) false
                  (fun b rest _ => bxIs b e1 c1 e2 c2 e3 c3 && k (Nat.shiftRight s 2) rest) l)
                (k (Nat.shiftRight s 2) l)
                (boxOut e1 c1 e2 c2 e3 c3 R.cuts))
            t')
          t)
        (Nat.land s 3))

/-- The master trees of the boxes with the numbers `b, b + 1, …` of the grid of the level `lv` (numbered as in
`groupGo`). The trees follow one another in the number `s`, and at the end the list of the boxes is empty. -/
noncomputable def masterGo (R : Run) (lv : Nat) : Nat → Nat → Nat → List Bx → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Bx → Bool)
    (fun _ _ l => isNil l)
    (fun _ ih b s l =>
      master R R.fuel s lv (Nat.div b (Nat.mul (Nat.shiftLeft 2 lv) (Nat.shiftLeft 2 lv)))
        lv (Nat.mod (Nat.div b (Nat.shiftLeft 2 lv)) (Nat.shiftLeft 2 lv)) lv (Nat.mod b (Nat.shiftLeft 2 lv)) l
        (fun s' l' => ih (Nat.succ b) s' l'))

/-- The checker of the master tree of a run: the master trees of all boxes of the grid of the level `lv`. Their
leaves are the boxes of the list, in its order, and boxes on which a cut fails. -/
noncomputable def masterOk (R : Run) (lv s : Nat) (boxes : List Bx) : Bool :=
  masterGo R lv (Nat.mul (Nat.mul (Nat.shiftLeft 2 lv) (Nat.shiftLeft 2 lv)) (Nat.shiftLeft 2 lv)) 0 s boxes

end N14.Box
