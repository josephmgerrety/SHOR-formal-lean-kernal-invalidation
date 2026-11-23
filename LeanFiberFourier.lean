import LeanFiberVariance
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace LeanFiberFourier

open scoped BigOperators

variable {n : Nat} [NeZero n]

def rawNumerator {K E : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    (chi : AddChar (ZMod n) K) (e : ZMod n → ZMod n → E)
    (k u v t : ZMod n) : E :=
  ∑ b : ZMod n, ∑ a : ZMod n,
    if a - k * b = t then chi (u * a + v * b) • e a b else 0

def amplitude {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E]
    (chi : AddChar (ZMod n) K) (e : ZMod n → ZMod n → E)
    (k u v t : ZMod n) : E :=
  ((n : K) ^ 2)⁻¹ • rawNumerator chi e k u v t

theorem raw_fiber_formula {K E : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    (chi : AddChar (ZMod n) K) (e : ZMod n → ZMod n → E)
    (k u v t : ZMod n) :
    rawNumerator chi e k u v t =
      chi (u * t) • ∑ b : ZMod n,
        chi ((k * u + v) * b) • e (t + k * b) b := by
  classical
  unfold rawNumerator
  simp only [sub_eq_iff_eq_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [show u * (t + k * b) + v * b =
    u * t + (k * u + v) * b by ring]
  rw [AddChar.map_add_eq_mul, mul_smul]

theorem raw_zero_frequencies {K E : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    (chi : AddChar (ZMod n) K) (e : ZMod n → ZMod n → E)
    (k t : ZMod n) :
    rawNumerator chi e k 0 0 t =
      ∑ b : ZMod n, e (t + k * b) b := by
  rw [raw_fiber_formula]
  simp

theorem standard_character_norm (x : ZMod n) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle x).norm_coe

theorem standard_character_sum (s : ZMod n) :
    (∑ b : ZMod n, ZMod.stdAddChar (s * b)) =
      if s = 0 then (n : Complex) else 0 := by
  by_cases hs : s = 0
  · subst s
    simp
  · simpa [hs, mul_comm] using
      AddChar.sum_mulShift s (ZMod.isPrimitive_stdAddChar n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Complex E]

theorem graph_preparation_normalized
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∑ a : ZMod n, ∑ b : ZMod n, ∑ t : ZMod n,
      ‖(if a - k * b = t then (n : Complex)⁻¹ • e a b else 0)‖ ^ 2) = 1 := by
  have hn : (n : Real) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp [apply_ite, norm_smul, hunit, ZMod.card, hn, pow_two]

theorem amplitude_norm_sq (e : ZMod n → ZMod n → E)
    (k u v t : ZMod n) :
    ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2 =
      ‖rawNumerator ZMod.stdAddChar e k u v t‖ ^ 2 / (n : Real) ^ 4 := by
  simp only [amplitude, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
  ring

theorem fourier_pair_probability (e : ZMod n → ZMod n → E)
    (k u v : ZMod n) :
    (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
      (∑ t : ZMod n,
        ‖∑ b : ZMod n, ZMod.stdAddChar ((k * u + v) * b) •
          e (t + k * b) b‖ ^ 2) / (n : Real) ^ 4 := by
  simp_rw [amplitude_norm_sq, raw_fiber_formula, norm_smul,
    standard_character_norm, one_mul]
  rw [Finset.sum_div]

theorem zero_pair_probability (e : ZMod n → ZMod n → E)
    (k : ZMod n) :
    (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k 0 0 t‖ ^ 2) =
      (∑ t : ZMod n, ‖∑ b : ZMod n, e (t + k * b) b‖ ^ 2) /
        (n : Real) ^ 4 := by
  simp_rw [amplitude_norm_sq, raw_zero_frequencies]
  rw [Finset.sum_div]

theorem raw_of_fiber_constant (e : ZMod n → ZMod n → E)
    (k : ZMod n)
    (hf : ∀ t b b', e (t + k * b) b = e (t + k * b') b')
    (u v t : ZMod n) :
    rawNumerator ZMod.stdAddChar e k u v t =
      ZMod.stdAddChar (u * t) •
        ((if k * u + v = 0 then (n : Complex) else 0) • e t 0) := by
  have hc (b : ZMod n) : e (t + k * b) b = e t 0 := by
    simpa using hf t b 0
  rw [raw_fiber_formula]
  simp_rw [hc]
  rw [← Finset.sum_smul, standard_character_sum]

theorem ideal_pair_law_of_fiber_constant
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1)
    (hf : ∀ t b b', e (t + k * b) b = e (t + k * b') b')
    (u v : ZMod n) :
    (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
      if k * u + v = 0 then 1 / (n : Real) else 0 := by
  have hn : (n : Real) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hnorm (t : ZMod n) :
      ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2 =
        if k * u + v = 0 then 1 / (n : Real) ^ 2 else 0 := by
    rw [amplitude_norm_sq, raw_of_fiber_constant e k hf]
    by_cases hs : k * u + v = 0
    · simp only [hs, ite_true, norm_smul, standard_character_norm,
        Complex.norm_natCast, hunit, mul_one, one_mul]
      field_simp
    · simp [hs]
  simp_rw [hnorm]
  by_cases hs : k * u + v = 0
  · simp only [hs, ite_true, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    field_simp
  · simp [hs]

theorem line_probability_formula
    (e : ZMod n → ZMod n → E) (k : ZMod n) :
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      (∑ t : ZMod n, ‖∑ b : ZMod n, e (t + k * b) b‖ ^ 2) /
        (n : Real) ^ 3 := by
  have hn : (n : Real) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hu (u t : ZMod n) :
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2 =
        ‖∑ b : ZMod n, e (t + k * b) b‖ ^ 2 / (n : Real) ^ 4 := by
    rw [amplitude_norm_sq, raw_fiber_formula]
    simp only [add_neg_cancel, zero_mul, AddChar.map_zero_eq_one,
      one_smul, norm_smul, standard_character_norm, one_mul]
  simp_rw [hu]
  rw [← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

theorem line_probability_one_iff_fiber_constant
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) = 1 ↔
      ∀ t b b', e (t + k * b) b = e (t + k * b') b' := by
  rw [line_probability_formula]
  have hv := LeanFiberVariance.fiber_coherence_iff (K := Complex)
    (fun t b : ZMod n => e (t + k * b) b)
    (fun t b => hunit (t + k * b) b)
  simpa only [ZMod.card, ← pow_succ'] using hv

theorem ideal_pair_law_iff_fiber_constant
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∀ u v : ZMod n,
      (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
        if k * u + v = 0 then 1 / (n : Real) else 0) ↔
      ∀ t b b', e (t + k * b) b = e (t + k * b') b' := by
  constructor
  · intro hlaw
    apply (line_probability_one_iff_fiber_constant e k hunit).mp
    have hline (u : ZMod n) :
        (∑ t : ZMod n,
          ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
          1 / (n : Real) := by
      simpa using hlaw u (-(k * u))
    simp_rw [hline]
    simp [ZMod.card, NeZero.ne n]
  · intro hf u v
    exact ideal_pair_law_of_fiber_constant e k hunit hf u v

theorem exact_fourier_line_defect
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    1 - (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      (∑ t : ZMod n, ∑ b : ZMod n, ∑ b' : ZMod n,
        ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2) /
        (2 * (n : Real) ^ 3) := by
  rw [line_probability_formula]
  have hv := LeanFiberVariance.exact_coherence_defect (K := Complex)
    (fun t b : ZMod n => e (t + k * b) b)
    (fun t b => hunit (t + k * b) b)
  simpa only [ZMod.card, ← mul_assoc, ← pow_succ', mul_assoc] using hv

omit [NeZero n] [NormedAddCommGroup E] [InnerProductSpace Complex E] in
theorem fiber_constant_iff_output_factor
    (e : ZMod n → ZMod n → E) (k : ZMod n) :
    (∀ t b b', e (t + k * b) b = e (t + k * b') b') ↔
      ∃ f : ZMod n → E, ∀ a b, e a b = f (a - k * b) := by
  constructor
  · intro hf
    refine ⟨fun t => e t 0, ?_⟩
    intro a b
    simpa only [sub_add_cancel, mul_zero, add_zero] using hf (a - k * b) b 0
  · rintro ⟨f, hf⟩ t b b'
    simp only [hf, add_sub_cancel_right]

theorem ideal_pair_law_iff_output_factor
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1) :
    (∀ u v : ZMod n,
      (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
        if k * u + v = 0 then 1 / (n : Real) else 0) ↔
      ∃ f : ZMod n → E, ∀ a b, e a b = f (a - k * b) := by
  rw [ideal_pair_law_iff_fiber_constant e k hunit,
    fiber_constant_iff_output_factor]

theorem unequal_fiber_vectors_forbid_ideal_law
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1)
    (t b b' : ZMod n) (hne : e (t + k * b) b ≠ e (t + k * b') b') :
    ¬ (∀ u v : ZMod n,
      (∑ t : ZMod n, ‖amplitude ZMod.stdAddChar e k u v t‖ ^ 2) =
        if k * u + v = 0 then 1 / (n : Real) else 0) := by
  intro hideal
  exact hne ((ideal_pair_law_iff_fiber_constant e k hunit).mp hideal t b b')

#print axioms raw_fiber_formula
#print axioms raw_zero_frequencies
#print axioms standard_character_norm
#print axioms standard_character_sum
#print axioms graph_preparation_normalized
#print axioms amplitude_norm_sq
#print axioms fourier_pair_probability
#print axioms zero_pair_probability
#print axioms raw_of_fiber_constant
#print axioms ideal_pair_law_of_fiber_constant
#print axioms line_probability_formula
#print axioms line_probability_one_iff_fiber_constant
#print axioms ideal_pair_law_iff_fiber_constant
#print axioms exact_fourier_line_defect
#print axioms fiber_constant_iff_output_factor
#print axioms ideal_pair_law_iff_output_factor
#print axioms unequal_fiber_vectors_forbid_ideal_law

end LeanFiberFourier
