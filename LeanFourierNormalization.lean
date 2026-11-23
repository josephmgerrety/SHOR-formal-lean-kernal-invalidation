import LeanFiberFourier
import LeanFourierParseval

namespace LeanFourierNormalization

open scoped BigOperators
open LeanFiberFourier

variable {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem shifted_parseval (f : ZMod n → E) (a : ZMod n) :
    (∑ s : ZMod n,
      ‖∑ b : ZMod n, ZMod.stdAddChar ((a + s) * b) • f b‖ ^ 2) =
      (n : ℝ) * ∑ b : ZMod n, ‖f b‖ ^ 2 := by
  calc
    (∑ s : ZMod n,
        ‖∑ b : ZMod n, ZMod.stdAddChar ((a + s) * b) • f b‖ ^ 2) =
      ∑ s : ZMod n,
        ‖∑ b : ZMod n, ZMod.stdAddChar (s * b) • f b‖ ^ 2 := by
          exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun s => rfl)
    _ = (n : ℝ) * ∑ b : ZMod n, ‖f b‖ ^ 2 :=
      LeanFourierParseval.vector_parseval f

theorem fixed_first_frequency_and_output_mass
    (e : ZMod n → ZMod n → E) (k u t : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∑ v : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
      1 / (n : ℝ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp_rw [amplitude_norm_sq, raw_fiber_formula, norm_smul,
    standard_character_norm, one_mul]
  rw [← Finset.sum_div, shifted_parseval]
  simp only [hunit, one_pow, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one]
  field_simp

theorem total_probability_one
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∑ u : ZMod n, ∑ v : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  calc
    (∑ u : ZMod n, ∑ v : ZMod n, ∑ t : ZMod n,
        ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
      ∑ u : ZMod n, ∑ t : ZMod n, ∑ v : ZMod n,
        ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_comm]
    _ = ∑ _u : ZMod n, ∑ _t : ZMod n, 1 / (n : ℝ) ^ 2 := by
          simp_rw [fixed_first_frequency_and_output_mass e k _ _ hunit]
    _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]
          field_simp

#print axioms shifted_parseval
#print axioms fixed_first_frequency_and_output_mass
#print axioms total_probability_one

end LeanFourierNormalization
