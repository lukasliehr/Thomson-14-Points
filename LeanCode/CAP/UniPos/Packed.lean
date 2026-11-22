module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import CAP.Core.PackedLemmas
public import CAP.UniPos.Kernel

/-!
# Polynomials with natural coefficients as packed numbers

Three lemmas that the soundness proofs of E3 and of E11 share: a polynomial with natural
coefficients at `2 ^ V` is the packed number of its coefficients (`eval_two_pow`), every
coefficient is at most the value at `1` (`coeff_le_eval_one`), and the test `geTest` compares the
slots of two packed numbers (`geTest_sound`).
-/

@[expose] public section

namespace CAP.UniPos

open Polynomial Finset

/-- A polynomial of degree below `m` at `2 ^ V` is the packed number of its coefficients. -/
theorem eval_two_pow (V m : ℕ) (F : ℕ[X]) (h : F.natDegree < m) : F.eval (2 ^ V) = packSum V m F.coeff := by
  rw [eval_eq_sum_range' h]
  unfold packSum
  exact sum_congr rfl fun i _ => by rw [pow_mul]

/-- Every coefficient is at most the sum of the coefficients. -/
theorem coeff_le_eval_one (F : ℕ[X]) (i : ℕ) : F.coeff i ≤ F.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hi : i ∈ range (F.natDegree + 1)
  · exact single_le_sum (f := fun j => F.coeff j) (fun _ _ => Nat.zero_le _) hi
  · have hlt : F.natDegree < i := by
      rw [mem_range, not_lt] at hi
      omega
    rw [coeff_eq_zero_of_natDegree_lt hlt]
    exact Nat.zero_le _

/-- If `geTest` accepts two packed numbers with slots below `2 ^ (V - 1)`, every slot of the
second one is at most the corresponding slot of the first one. -/
theorem geTest_sound (V m : ℕ) (bp bn : ℕ → ℕ) (hV : 1 ≤ V) (hp : ∀ i, i < m → bp i < 2 ^ (V - 1))
    (hn : ∀ i, i < m → bn i < 2 ^ (V - 1)) (h : geTest V m (packSum V m bp) (packSum V m bn) = true) :
    ∀ i, i < m → bn i ≤ bp i := by
  have h2 : 2 ^ V = 2 * 2 ^ (V - 1) := two_pow_pred hV
  have hV0 : 0 < V := hV
  unfold geTest at h
  rw [Bool.and_eq_true] at h
  have hD : packSum V m bp - packSum V m bn + packSum V m bn = packSum V m bp :=
    Nat.eq_of_beq_eq_true h.1
  have hm : (packSum V m bp - packSum V m bn) &&& ((1 <<< V - 1 <<< (V - 1)) * ones V m) = 0 :=
    Nat.eq_of_beq_eq_true h.2
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, ones_eq V m hV0] at hm
  -- the difference as a packed number
  have hlt : packSum V m bp - packSum V m bn < 2 ^ (V * m) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (packSum_lt V m bp (fun i hi => by have := hp i hi; omega))
  have hslot := packSum_slot V m _ hlt
  rw [← hslot] at hm
  have hd := slots_lt_of_and_hi V (V - 1) m _ (Nat.sub_le V 1)
    (fun j _ => slot_lt V (packSum V m bp - packSum V m bn) j) hm
  -- digits
  have heq : packSum V m (fun j => slot V (packSum V m bp - packSum V m bn) j + bn j) = packSum V m bp := by
    rw [packSum_add, hslot, hD]
  intro i hi
  have := packSum_injective V m _ bp
    (fun j hj => by
      have a := hd j hj
      have b := hn j hj
      show slot V (packSum V m bp - packSum V m bn) j + bn j < 2 ^ V
      omega)
    (fun j hj => by have := hp j hj; omega) heq i hi
  omega

end CAP.UniPos
