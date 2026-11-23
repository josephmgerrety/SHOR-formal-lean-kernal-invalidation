import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace LeanFourierParseval

open scoped BigOperators

variable {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem standard_character_conjugate (x : ZMod n) :
    starRingEnd ℂ (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (by simp [ZMod.stdAddChar_apply])).symm

theorem standard_character_product (s b c : ZMod n) :
    starRingEnd ℂ (ZMod.stdAddChar (s * b)) * ZMod.stdAddChar (s * c) =
      ZMod.stdAddChar (s * (c - b)) := by
  rw [standard_character_conjugate, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem standard_character_sum (x : ZMod n) :
    (∑ s : ZMod n, ZMod.stdAddChar (s * x)) =
      if x = 0 then (n : ℂ) else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · rw [ite_eq_right hx]
    simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n hx)

theorem twisted_inner (s b c : ZMod n) (v w : E) :
    inner ℂ (ZMod.stdAddChar (s * b) • v)
      (ZMod.stdAddChar (s * c) • w) =
      ZMod.stdAddChar (s * (c - b)) * inner ℂ v w := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc,
    standard_character_product]

theorem fourier_inner_sum (v w : ZMod n → E) :
    (∑ s : ZMod n,
      inner ℂ (∑ b : ZMod n, ZMod.stdAddChar (s * b) • v b)
        (∑ c : ZMod n, ZMod.stdAddChar (s * c) • w c)) =
      (n : ℂ) * ∑ b : ZMod n, inner ℂ (v b) (w b) := by
  classical
  simp_rw [sum_inner, inner_sum, twisted_inner]
  calc
    (∑ s : ZMod n, ∑ b : ZMod n, ∑ c : ZMod n,
        ZMod.stdAddChar (s * (c - b)) * inner ℂ (v b) (w c)) =
      ∑ b : ZMod n, ∑ c : ZMod n, ∑ s : ZMod n,
        ZMod.stdAddChar (s * (c - b)) * inner ℂ (v b) (w c) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b : ZMod n, ∑ c : ZMod n,
        (if c = b then (n : ℂ) else 0) * inner ℂ (v b) (w c) := by
          simp only [← Finset.sum_mul, standard_character_sum, sub_eq_zero]
    _ = (n : ℂ) * ∑ b : ZMod n, inner ℂ (v b) (w b) := by
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true, Finset.mul_sum]

theorem vector_parseval (v : ZMod n → E) :
    (∑ s : ZMod n,
      ‖∑ b : ZMod n, ZMod.stdAddChar (s * b) • v b‖ ^ 2) =
      (n : ℝ) * ∑ b : ZMod n, ‖v b‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (fourier_inner_sum v v)
  simpa only [map_sum, RCLike.mul_re, RCLike.natCast_re,
    RCLike.natCast_im, zero_mul, sub_zero,
    ← norm_sq_eq_re_inner] using h

#print axioms standard_character_conjugate
#print axioms standard_character_product
#print axioms standard_character_sum
#print axioms twisted_inner
#print axioms fourier_inner_sum
#print axioms vector_parseval

end LeanFourierParseval
