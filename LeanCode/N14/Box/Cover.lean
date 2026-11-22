module

public import N14.Box.Table

/-!
# T7, the slack on a domain: the cover, and the theorem of a run

**Theorem** (`run_sound`). Let the parameters of a run and the tables of its three coordinates be accepted, and
let every box of the grid of the level `lv` belong to a group that the checker accepts (`groupOk`). Then

  `0 ≤ M(x) + U₁(x₁) + U₂(x₂) + U₃(x₃)`

at every point `x` of `[-1, 1)³` at which the Gram polynomial and the functions of all cuts of the run are
nonnegative. Here `M` is the polynomial whose coefficients are the slots of `R.PpM` minus the bias, and `U_a` is
the function of the table of the coordinate `a` (`tabFn`); their sum is `slackFn`.

`cover_sound`: an accepted cover of a box gives the statement of the cells at all points of the box, since a
point of a box lies in one of its halves, and a box that the checker discards violates a cut at all of its
points (`cutOut_sound`). `group_sound`: the boxes of a group. `grid3`: every point of `[-1, 1]³` lies in a box of
the grid.
-/

@[expose] public section

namespace N14.Box

open CAP CAP.Bernstein Finset

/-- The point `t` lies in the interval with the level `e` and the position `c`. -/
def InI (e c : ℕ) (t : ℝ) : Prop := (c : ℝ) / 2 ^ e - 1 ≤ t ∧ t ≤ ((c : ℝ) + 1) / 2 ^ e - 1

/-- A point of an interval lies in one of its halves. -/
theorem InI_split (e c : ℕ) (t : ℝ) (h : InI e c t) : InI (e + 1) (2 * c) t ∨ InI (e + 1) (2 * c + 1) t := by
  obtain ⟨h1, h2⟩ := h
  have hp : (0 : ℝ) < 2 ^ e := by positivity
  have e1 : ((2 * c : ℕ) : ℝ) / 2 ^ (e + 1) = (c : ℝ) / 2 ^ e := by
    rw [pow_succ]
    push_cast
    field_simp
  have e2 : (((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (e + 1) = ((c : ℝ) + 1) / 2 ^ e := by
    rw [pow_succ]
    push_cast
    field_simp
    ring
  have e3 : (((2 * c : ℕ) : ℝ) + 1) / 2 ^ (e + 1) = ((2 * c + 1 : ℕ) : ℝ) / 2 ^ (e + 1) := by
    push_cast
    rfl
  rcases le_total t ((((2 * c : ℕ) : ℝ) + 1) / 2 ^ (e + 1) - 1) with ht | ht
  · exact Or.inl ⟨by rw [e1]; exact h1, ht⟩
  · exact Or.inr ⟨by rw [← e3]; exact ht, by rw [e2]; exact h2⟩

/-- The value of the polynomial constraint with the number `Pp` of a run: the polynomial `g` for which the slots
of `Pp` are the biased coefficients of `-2 ^ sg * g`. -/
noncomputable def polyVal (R : Run) (Pp : ℕ) (x1 x2 x3 : ℝ) : ℝ :=
  -pEval (boxP R R.aG R.AG 0 0 0) Pp x1 x2 x3 / 2 ^ R.sg

/-- The domain of a run: the three coordinates are below `1`, and the Gram polynomial, the functions of all
cuts and the polynomial constraints (excluded balls, ellipsoids) are nonnegative. -/
def Dom (R : Run) (x1 x2 x3 : ℝ) : Prop :=
  x1 < 1 ∧ x2 < 1 ∧ x3 < 1 ∧ 0 ≤ gram x1 x2 x3 ∧ (∀ cut ∈ R.cuts, 0 ≤ cutVal cut x1 x2 x3) ∧
    ∀ Pp ∈ R.polys, 0 ≤ polyVal R Pp x1 x2 x3

theorem sel_InI (a e1 c1 e2 c2 e3 c3 : ℕ) (x1 x2 x3 : ℝ) (h1 : InI e1 c1 x1) (h2 : InI e2 c2 x2)
    (h3 : InI e3 c3 x3) : InI (sel a e1 e2 e3) (sel a c1 c2 c3) (co a x1 x2 x3) := by
  rcases a with _ | _ | a
  · exact h1
  · exact h2
  · exact h3

/-- A box that the checker discards for a cut violates the cut at all of its points. -/
theorem cutOut_sound (c : Cut) (hvd : 1 ≤ c.vd) (e1 c1 e2 c2 e3 c3 : ℕ)
    (h : cutOut c e1 c1 e2 c2 e3 c3 = true) (x1 x2 x3 : ℝ) (h1 : InI e1 c1 x1) (h2 : InI e2 c2 x2)
    (h3 : InI e3 c3 x3) : cutVal c x1 x2 x3 < 0 := by
  obtain ⟨ha1, ha2⟩ := sel_InI c.a e1 c1 e2 c2 e3 c3 x1 x2 x3 h1 h2 h3
  obtain ⟨hb1, hb2⟩ := sel_InI c.b e1 c1 e2 c2 e3 c3 x1 x2 x3 h1 h2 h3
  have hpa : (0 : ℝ) < 2 ^ (sel c.a e1 e2 e3) := by positivity
  have hpb : (0 : ℝ) < 2 ^ (sel c.b e1 e2 e3) := by positivity
  have hd : (0 : ℝ) < c.vd := by exact_mod_cast hvd
  unfold cutOut at h
  unfold cutVal
  rcases hk : c.kind with _ | _ | kk
  · rw [hk] at h
    have h' : Nat.blt ((sel c.a c1 c2 c3 + 1) * c.vd) (c.vn <<< (sel c.a e1 e2 e3)) = true := h
    rw [Nat.blt_eq, Nat.shiftLeft_eq] at h'
    have hr : (((sel c.a c1 c2 c3 : ℕ) : ℝ) + 1) * c.vd < (c.vn : ℝ) * 2 ^ (sel c.a e1 e2 e3) := by
      exact_mod_cast h'
    have hq : (((sel c.a c1 c2 c3 : ℕ) : ℝ) + 1) / 2 ^ (sel c.a e1 e2 e3) < (c.vn : ℝ) / c.vd := by
      rw [div_lt_div_iff₀ hpa hd]
      exact hr
    rw [if_pos rfl]
    linarith
  · rw [hk] at h
    have h' : Nat.blt (c.vn <<< (sel c.a e1 e2 e3)) (sel c.a c1 c2 c3 * c.vd) = true := h
    rw [Nat.blt_eq, Nat.shiftLeft_eq] at h'
    have hr : (c.vn : ℝ) * 2 ^ (sel c.a e1 e2 e3) < ((sel c.a c1 c2 c3 : ℕ) : ℝ) * c.vd := by
      exact_mod_cast h'
    have hq : (c.vn : ℝ) / c.vd < ((sel c.a c1 c2 c3 : ℕ) : ℝ) / 2 ^ (sel c.a e1 e2 e3) := by
      rw [div_lt_div_iff₀ hd hpa]
      exact hr
    rw [if_neg (by omega), if_pos rfl]
    linarith
  · rw [hk] at h
    have h' : Nat.blt ((sel c.a c1 c2 c3 + 1) <<< (sel c.b e1 e2 e3))
        ((sel c.b c1 c2 c3) <<< (sel c.a e1 e2 e3)) = true := h
    rw [Nat.blt_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq] at h'
    have hr : (((sel c.a c1 c2 c3 : ℕ) : ℝ) + 1) * 2 ^ (sel c.b e1 e2 e3)
        < ((sel c.b c1 c2 c3 : ℕ) : ℝ) * 2 ^ (sel c.a e1 e2 e3) := by
      exact_mod_cast h'
    have hq : (((sel c.a c1 c2 c3 : ℕ) : ℝ) + 1) / 2 ^ (sel c.a e1 e2 e3)
        < ((sel c.b c1 c2 c3 : ℕ) : ℝ) / 2 ^ (sel c.b e1 e2 e3) := by
      rw [div_lt_div_iff₀ hpa hpb]
      exact hr
    rw [if_neg (by omega), if_neg (by omega)]
    linarith

/-- A box that the checker discards violates a cut at all of its points. -/
theorem boxOut_sound (e1 c1 e2 c2 e3 c3 : ℕ) : ∀ l : List Cut, (∀ c ∈ l, 1 ≤ c.vd) →
    boxOut e1 c1 e2 c2 e3 c3 l = true → ∀ x1 x2 x3 : ℝ, InI e1 c1 x1 → InI e2 c2 x2 → InI e3 c3 x3 →
      ∃ c ∈ l, cutVal c x1 x2 x3 < 0 := by
  intro l
  induction l with
  | nil => exact fun _ h => absurd (show false = true from h) (by decide)
  | cons c l ih =>
    intro hvd h x1 x2 x3 h1 h2 h3
    have h' : (cutOut c e1 c1 e2 c2 e3 c3 || boxOut e1 c1 e2 c2 e3 c3 l) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with hc | hl
    · exact ⟨c, List.mem_cons_self, cutOut_sound c (hvd c List.mem_cons_self) _ _ _ _ _ _ hc x1 x2 x3 h1 h2 h3⟩
    · obtain ⟨c', hc', hv⟩ := ih (fun c' hc' => hvd c' (List.mem_cons_of_mem _ hc')) hl x1 x2 x3 h1 h2 h3
      exact ⟨c', List.mem_cons_of_mem _ hc', hv⟩

theorem cover_succ (R : Run) (f s e1 c1 e2 c2 e3 c3 : ℕ) (l : List Cell) (k : ℕ → List Cell → Bool) :
    cover R (f + 1) s e1 c1 e2 c2 e3 c3 l k =
      Nat.rec (motive := fun _ => Bool)
        (cover R f (Nat.shiftRight s 2) (Nat.succ e1) (Nat.mul 2 c1) e2 c2 e3 c3 l
          (fun s' l' => cover R f s' (Nat.succ e1) (Nat.succ (Nat.mul 2 c1)) e2 c2 e3 c3 l' k))
        (fun t _ => Nat.rec (motive := fun _ => Bool)
          (cover R f (Nat.shiftRight s 2) e1 c1 (Nat.succ e2) (Nat.mul 2 c2) e3 c3 l
            (fun s' l' => cover R f s' e1 c1 (Nat.succ e2) (Nat.succ (Nat.mul 2 c2)) e3 c3 l' k))
          (fun t' _ => Nat.rec (motive := fun _ => Bool)
            (cover R f (Nat.shiftRight s 2) e1 c1 e2 c2 (Nat.succ e3) (Nat.mul 2 c3) l
              (fun s' l' => cover R f s' e1 c1 e2 c2 (Nat.succ e3) (Nat.succ (Nat.mul 2 c3)) l' k))
            (fun _ _ =>
              Bool.rec (motive := fun _ => Bool)
                (List.rec (motive := fun _ => Bool) false
                  (fun c rest _ => cellIs R c e1 c1 e2 c2 e3 c3 && cellOk R c && k (Nat.shiftRight s 2) rest) l)
                (k (Nat.shiftRight s 2) l)
                (boxOut e1 c1 e2 c2 e3 c3 R.cuts))
            t')
          t)
        (Nat.land s 3) := rfl

/-- **The cover of a box.** If the checker accepts the cover of a box, a statement that holds on every accepted
cell at the points of the domain holds at all points of the domain in the box; and the test of the rest is
accepted. -/
theorem cover_sound (R : Run) (hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd) (Q : ℝ → ℝ → ℝ → Prop)
    (hcell : ∀ c : Cell, cellOk R c = true → ∀ x1 x2 x3 : ℝ, InIv (ent R.t1 c.i) x1 → InIv (ent R.t2 c.j) x2 →
      InIv (ent R.t3 c.k) x3 → Dom R x1 x2 x3 → Q x1 x2 x3) :
    ∀ (fuel s e1 c1 e2 c2 e3 c3 : ℕ) (l : List Cell) (k : ℕ → List Cell → Bool),
      cover R fuel s e1 c1 e2 c2 e3 c3 l k = true →
      (∀ x1 x2 x3 : ℝ, InI e1 c1 x1 → InI e2 c2 x2 → InI e3 c3 x3 → Dom R x1 x2 x3 → Q x1 x2 x3) ∧
        ∃ s' l', k s' l' = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro s e1 c1 e2 c2 e3 c3 l k h
    exact absurd (show false = true from h) (by decide)
  | succ f ih =>
    intro s e1 c1 e2 c2 e3 c3 l k h
    rw [cover_succ] at h
    generalize Nat.land s 3 = t at h
    rcases t with _ | _ | _ | t
    · have h0 : cover R f (Nat.shiftRight s 2) (e1 + 1) (2 * c1) e2 c2 e3 c3 l
          (fun s' l' => cover R f s' (e1 + 1) (2 * c1 + 1) e2 c2 e3 c3 l' k) = true := h
      obtain ⟨gl, s1, l1, h1⟩ := ih _ _ _ _ _ _ _ _ _ h0
      obtain ⟨gr, s2, l2, h2⟩ := ih _ _ _ _ _ _ _ _ _ h1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2⟩
      rcases InI_split e1 c1 x1 hx1 with hL | hR
      · exact gl x1 x2 x3 hL hx2 hx3 hD
      · exact gr x1 x2 x3 hR hx2 hx3 hD
    · have h0 : cover R f (Nat.shiftRight s 2) e1 c1 (e2 + 1) (2 * c2) e3 c3 l
          (fun s' l' => cover R f s' e1 c1 (e2 + 1) (2 * c2 + 1) e3 c3 l' k) = true := h
      obtain ⟨gl, s1, l1, h1⟩ := ih _ _ _ _ _ _ _ _ _ h0
      obtain ⟨gr, s2, l2, h2⟩ := ih _ _ _ _ _ _ _ _ _ h1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2⟩
      rcases InI_split e2 c2 x2 hx2 with hL | hR
      · exact gl x1 x2 x3 hx1 hL hx3 hD
      · exact gr x1 x2 x3 hx1 hR hx3 hD
    · have h0 : cover R f (Nat.shiftRight s 2) e1 c1 e2 c2 (e3 + 1) (2 * c3) l
          (fun s' l' => cover R f s' e1 c1 e2 c2 (e3 + 1) (2 * c3 + 1) l' k) = true := h
      obtain ⟨gl, s1, l1, h1⟩ := ih _ _ _ _ _ _ _ _ _ h0
      obtain ⟨gr, s2, l2, h2⟩ := ih _ _ _ _ _ _ _ _ _ h1
      refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, s2, l2, h2⟩
      rcases InI_split e3 c3 x3 hx3 with hL | hR
      · exact gl x1 x2 x3 hx1 hx2 hL hD
      · exact gr x1 x2 x3 hx1 hx2 hR hD
    · have h0 : Bool.rec (motive := fun _ => Bool)
          (List.rec (motive := fun _ => Bool) false
            (fun c rest _ => cellIs R c e1 c1 e2 c2 e3 c3 && cellOk R c && k (Nat.shiftRight s 2) rest) l)
          (k (Nat.shiftRight s 2) l) (boxOut e1 c1 e2 c2 e3 c3 R.cuts) = true := h
      cases hb : boxOut e1 c1 e2 c2 e3 c3 R.cuts with
      | true =>
        rw [hb] at h0
        refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, _, _, h0⟩
        obtain ⟨c, hc, hv⟩ := boxOut_sound e1 c1 e2 c2 e3 c3 R.cuts hvd hb x1 x2 x3 hx1 hx2 hx3
        have := hD.2.2.2.2.1 c hc
        linarith
      | false =>
        rw [hb] at h0
        cases l with
        | nil => exact absurd (show false = true from h0) (by decide)
        | cons c rest =>
          have h1 : (cellIs R c e1 c1 e2 c2 e3 c3 && cellOk R c && k (Nat.shiftRight s 2) rest) = true := h0
          rw [Bool.and_eq_true, Bool.and_eq_true] at h1
          obtain ⟨⟨his, hok⟩, hk⟩ := h1
          have his' : (Nat.beq (ent R.t1 c.i).e e1 && Nat.beq (ent R.t1 c.i).c c1
              && Nat.beq (ent R.t2 c.j).e e2 && Nat.beq (ent R.t2 c.j).c c2
              && Nat.beq (ent R.t3 c.k).e e3 && Nat.beq (ent R.t3 c.k).c c3) = true := his
          simp only [Bool.and_eq_true] at his'
          obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := his'
          refine ⟨fun x1 x2 x3 hx1 hx2 hx3 hD => ?_, _, _, hk⟩
          refine hcell c hok x1 x2 x3 ?_ ?_ ?_ hD
          · show InI (ent R.t1 c.i).e (ent R.t1 c.i).c x1
            rw [Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2]
            exact hx1
          · show InI (ent R.t2 c.j).e (ent R.t2 c.j).c x2
            rw [Nat.eq_of_beq_eq_true a3, Nat.eq_of_beq_eq_true a4]
            exact hx2
          · show InI (ent R.t3 c.k).e (ent R.t3 c.k).c x3
            rw [Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6]
            exact hx3

/-- The point lies in the box with the number `b` of the grid of the level `lv`. -/
def InGrid (lv b : ℕ) (x1 x2 x3 : ℝ) : Prop :=
  InI lv (b / ((2 <<< lv) * (2 <<< lv))) x1 ∧ InI lv (b / (2 <<< lv) % (2 <<< lv)) x2 ∧ InI lv (b % (2 <<< lv)) x3

/-- **A group of boxes of the grid.** -/
theorem group_sound (R : Run) (hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd) (Q : ℝ → ℝ → ℝ → Prop)
    (hcell : ∀ c : Cell, cellOk R c = true → ∀ x1 x2 x3 : ℝ, InIv (ent R.t1 c.i) x1 → InIv (ent R.t2 c.j) x2 →
      InIv (ent R.t3 c.k) x3 → Dom R x1 x2 x3 → Q x1 x2 x3) (lv : ℕ) :
    ∀ (cnt b s : ℕ) (l : List Cell), groupGo R lv cnt b s l = true →
      ∀ b', b ≤ b' → b' < b + cnt → ∀ x1 x2 x3 : ℝ, InGrid lv b' x1 x2 x3 → Dom R x1 x2 x3 → Q x1 x2 x3 := by
  intro cnt
  induction cnt with
  | zero =>
    intro b s l _ b' h1 h2
    omega
  | succ cnt ih =>
    intro b s l h b' h1 h2 x1 x2 x3 hx hD
    have h0 : cover R R.fuel s lv (b / ((2 <<< lv) * (2 <<< lv))) lv (b / (2 <<< lv) % (2 <<< lv)) lv
        (b % (2 <<< lv)) l (fun s' l' => groupGo R lv cnt (b + 1) s' l') = true := h
    obtain ⟨g, s1, l1, hrest⟩ := cover_sound R hvd Q hcell _ _ _ _ _ _ _ _ _ _ h0
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact g x1 x2 x3 hx.1 hx.2.1 hx.2.2 hD
    · exact ih (b + 1) s1 l1 hrest b' hlt (by omega) x1 x2 x3 hx hD

/-- Every point of `[-1, 1]` lies in an interval of the level `lv`. -/
theorem grid1 : ∀ (lv : ℕ) (t : ℝ), -1 ≤ t → t ≤ 1 → ∃ c, c < 2 <<< lv ∧ InI lv c t := by
  intro lv
  induction lv with
  | zero =>
    intro t h1 h2
    rcases le_total t 0 with h | h
    · refine ⟨0, by decide, ?_, ?_⟩ <;> norm_num <;> linarith
    · refine ⟨1, by decide, ?_, ?_⟩ <;> norm_num <;> linarith
  | succ lv ih =>
    intro t h1 h2
    obtain ⟨c, hc, hI⟩ := ih t h1 h2
    have hm : 2 <<< (lv + 1) = 2 * (2 <<< lv) := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, pow_succ]
      ring
    rcases InI_split lv c t hI with h | h
    · exact ⟨2 * c, by omega, h⟩
    · exact ⟨2 * c + 1, by omega, h⟩

/-- Every point of `[-1, 1]³` lies in a box of the grid of the level `lv`. -/
theorem grid3 (lv : ℕ) (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h1' : x1 ≤ 1) (h2 : -1 ≤ x2) (h2' : x2 ≤ 1)
    (h3 : -1 ≤ x3) (h3' : x3 ≤ 1) :
    ∃ b, b < (2 <<< lv) * (2 <<< lv) * (2 <<< lv) ∧ InGrid lv b x1 x2 x3 := by
  obtain ⟨c1, hc1, i1⟩ := grid1 lv x1 h1 h1'
  obtain ⟨c2, hc2, i2⟩ := grid1 lv x2 h2 h2'
  obtain ⟨c3, hc3, i3⟩ := grid1 lv x3 h3 h3'
  unfold InGrid
  generalize 2 <<< lv = m at hc1 hc2 hc3 ⊢
  have hm : 0 < m := by omega
  have hlow : c2 * m + c3 < m * m := by nlinarith
  have e3 : (m * m * c1 + (c2 * m + c3)) % m = c3 := by
    have : m * m * c1 + (c2 * m + c3) = m * (m * c1 + c2) + c3 := by ring
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hc3]
  have e2 : (m * m * c1 + (c2 * m + c3)) / m % m = c2 := by
    have : m * m * c1 + (c2 * m + c3) = m * (m * c1 + c2) + c3 := by ring
    rw [this, Nat.mul_add_div hm, Nat.div_eq_of_lt hc3, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hc2]
  have e1 : (m * m * c1 + (c2 * m + c3)) / (m * m) = c1 := by
    rw [Nat.mul_add_div (Nat.mul_pos hm hm), Nat.div_eq_of_lt hlow, Nat.add_zero]
  refine ⟨m * m * c1 + (c2 * m + c3), by nlinarith, ?_, ?_, ?_⟩
  · rw [e1]
    exact i1
  · rw [e2]
    exact i2
  · rw [e3]
    exact i3

/-! ## The theorem of a run -/

/-- The slack of a run with the tables `U1`, `U2`, `U3` of its three coordinates, in the units of the run. -/
noncomputable def slackFn (R : Run) (U1 U2 U3 : Tab) (x1 x2 x3 : ℝ) : ℝ :=
  pEval (boxP R R.aH R.A 0 0 0) R.PpM x1 x2 x3 + tabFn U1 x1 + tabFn U2 x2 + tabFn U3 x3

/-- An interval with a table entry belongs to the list. -/
theorem ent_mem : ∀ (l : List Ent) (i : ℕ), 0 < (ent l i).T → ent l i ∈ l := by
  intro l
  induction l with
  | nil => exact fun i h => absurd (show (0 : ℕ) < 0 from h) (Nat.lt_irrefl 0)
  | cons x l ih =>
    intro i h
    cases i with
    | zero => exact List.mem_cons_self
    | succ i => exact List.mem_cons_of_mem _ (ih i h)

/-- The statement of an accepted cell for the slack of the run. -/
theorem cell_slack (R : Run) (hR : RunFit R) (U1 U2 U3 : Tab)
    (hU1 : U1.P.W = R.W ∧ U1.n = R.n) (hU2 : U2.P.W = R.W ∧ U2.n = R.n) (hU3 : U3.P.W = R.W ∧ U3.n = R.n)
    (ht1 : ∀ x ∈ R.t1, 0 < x.T → EntryGood U1 x) (ht2 : ∀ x ∈ R.t2, 0 < x.T → EntryGood U2 x)
    (ht3 : ∀ x ∈ R.t3, 0 < x.T → EntryGood U3 x) (c : Cell) (h : cellOk R c = true) (x1 x2 x3 : ℝ)
    (h1 : InIv (ent R.t1 c.i) x1) (h2 : InIv (ent R.t2 c.j) x2) (h3 : InIv (ent R.t3 c.k) x3)
    (hD : Dom R x1 x2 x3) : 0 ≤ slackFn R U1 U2 U3 x1 x2 x3 := by
  have h' : (Nat.blt 0 (ent R.t1 c.i).T && Nat.blt 0 (ent R.t2 c.j).T && Nat.blt 0 (ent R.t3 c.k).T
      && go R (boxP R R.aH R.A c.i c.j c.k) (binomJ (boxP R R.aH R.A c.i c.j c.k)) R.fuel c.tree
        (rootArr (boxP R R.aH R.A c.i c.j c.k) (cellPp R c.i c.j c.k)) (conArrs R c.i c.j c.k c.use)
        (fun _ => true)) = true := h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, _⟩ := h'
  have hpoly : ∀ Pp ∈ R.polys, pEval (boxP R R.aG R.AG 0 0 0) Pp x1 x2 x3 ≤ 0 := by
    intro Pp hPp
    have h0 := hD.2.2.2.2.2 Pp hPp
    unfold polyVal at h0
    have hS : (0 : ℝ) < 2 ^ R.sg := by positivity
    by_contra hc
    have := div_neg_of_neg_of_pos (neg_neg_of_pos (not_le.mp hc)) hS
    linarith
  have key := cell_sound R hR c h x1 x2 x3 h1 h2 h3 hD.2.2.2.1 hD.2.2.2.2.1 hpoly
  have g1 := ht1 _ (ent_mem R.t1 c.i p1) p1 x1 h1 hD.1
  have g2 := ht2 _ (ent_mem R.t2 c.j p2) p2 x2 h2 hD.2.1
  have g3 := ht3 _ (ent_mem R.t3 c.k p3) p3 x3 h3 hD.2.2.1
  rw [hU1.1, hU1.2] at g1
  rw [hU2.1, hU2.2] at g2
  rw [hU3.1, hU3.2] at g3
  have e : pEval (boxP R R.aH R.A c.i c.j c.k) R.PpM x1 x2 x3 = pEval (boxP R R.aH R.A 0 0 0) R.PpM x1 x2 x3 := rfl
  unfold slackFn
  rw [← e]
  linarith

/-- The boxes of the grid with the numbers `b0, …, N - 1` belong to accepted groups. -/
def Covered (R : Run) (lv b0 N : ℕ) : Prop :=
  ∀ b, b0 ≤ b → b < N → ∃ b1 cnt s l, groupOk R lv b1 cnt s l = true ∧ b1 ≤ b ∧ b < b1 + cnt

theorem covered_end (R : Run) (lv N : ℕ) : Covered R lv N N :=
  fun _ h1 h2 => absurd h2 (Nat.not_lt.mpr h1)

/-- An accepted group of the boxes `b0, …, b0 + cnt - 1` before the boxes from `b0 + cnt` on. -/
theorem covered_cons (R : Run) (lv b0 cnt N s : ℕ) (l : List Cell) (h : groupOk R lv b0 cnt s l = true)
    (rest : Covered R lv (b0 + cnt) N) : Covered R lv b0 N := by
  intro b h1 h2
  rcases Nat.lt_or_ge b (b0 + cnt) with hlt | hge
  · exact ⟨b0, cnt, s, l, h, h1, hlt⟩
  · exact rest b hge h2

/-- **The theorem of a run.** -/
theorem run_sound (R : Run) (hR : runOk R = true) (U1 U2 U3 : Tab)
    (hU1 : U1.P.W = R.W ∧ U1.n = R.n) (hU2 : U2.P.W = R.W ∧ U2.n = R.n) (hU3 : U3.P.W = R.W ∧ U3.n = R.n)
    (ht1 : tableOk U1 R.t1 = true) (ht2 : tableOk U2 R.t2 = true) (ht3 : tableOk U3 R.t3 = true) (lv N : ℕ)
    (hN : (2 <<< lv) * (2 <<< lv) * (2 <<< lv) = N) (hgroups : Covered R lv 0 N)
    (x1 x2 x3 : ℝ) (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3) (hD : Dom R x1 x2 x3) :
    0 ≤ slackFn R U1 U2 U3 x1 x2 x3 := by
  have hfit := runOk_fit R hR
  have hvd : ∀ c ∈ R.cuts, 1 ≤ c.vd := by
    intro c hc
    have h := hfit.cuts c hc
    have h' : (Nat.ble 1 c.vd
        && Nat.beq ((c.vn * (1 <<< R.sg)) / c.vd * c.vd) (c.vn * (1 <<< R.sg))
        && Nat.ble c.vn (2 * c.vd)) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h'
    exact h'.1.1
  obtain ⟨b, hb, hx⟩ := grid3 lv x1 x2 x3 h1 hD.1.le h2 hD.2.1.le h3 hD.2.2.1.le
  obtain ⟨b0, cnt, s, l, hg, hb0, hb1⟩ := hgroups b (Nat.zero_le b) (hN ▸ hb)
  exact group_sound R hvd (fun y1 y2 y3 => 0 ≤ slackFn R U1 U2 U3 y1 y2 y3)
    (cell_slack R hfit U1 U2 U3 hU1 hU2 hU3 (table_sound U1 R.t1 ht1) (table_sound U2 R.t2 ht2)
      (table_sound U3 R.t3 ht3))
    lv cnt b0 s l hg b hb0 hb1 x1 x2 x3 hx hD

end N14.Box
