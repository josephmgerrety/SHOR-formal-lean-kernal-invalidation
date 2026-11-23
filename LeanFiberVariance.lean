import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace LeanFiberVariance

open scoped BigOperators

variable {K E B T : Type*} [RCLike K]
variable [NormedAddCommGroup E] [InnerProductSpace K E]
variable [Fintype B] [Fintype T]

include K

theorem norm_sum_sq_as_double_inner (v : B → E) :
    ‖∑ b, v b‖ ^ 2 =
      ∑ b, ∑ b', RCLike.re (inner K (v b) (v b')) := by
  rw [norm_sq_eq_re_inner (𝕜 := K), sum_inner]
  simp only [inner_sum, map_sum]

theorem pairwise_variance (v : B → E) :
    (∑ b, ∑ b', ‖v b - v b'‖ ^ 2) =
      2 * ((Fintype.card B : ℝ) * (∑ b, ‖v b‖ ^ 2) -
        ‖∑ b, v b‖ ^ 2) := by
  simp_rw [norm_sub_sq (𝕜 := K)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [norm_sum_sq_as_double_inner (K := K)]
  simp only [← Finset.mul_sum]
  ring

theorem normalized_fiber_variance (e : T → B → E)
    (hunit : ∀ t b, ‖e t b‖ = 1) :
    (∑ t, ∑ b, ∑ b', ‖e t b - e t b'‖ ^ 2) =
      2 * ((Fintype.card T : ℝ) * (Fintype.card B : ℝ) ^ 2 -
        ∑ t, ‖∑ b, e t b‖ ^ 2) := by
  simp_rw [pairwise_variance (K := K), hunit, one_pow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

omit K in
theorem fiber_variance_zero_iff (e : T → B → E) :
    (∑ t, ∑ b, ∑ b', ‖e t b - e t b'‖ ^ 2) = 0 ↔
      ∀ t b b', e t b = e t b' := by
  constructor
  · intro hz t b b'
    have ht : (∑ b, ∑ b', ‖e t b - e t b'‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)))).mp hz t
          (Finset.mem_univ t)
    have hb : (∑ b', ‖e t b - e t b'‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))).mp ht b
          (Finset.mem_univ b)
    have hbb : ‖e t b - e t b'‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => sq_nonneg _)).mp hb b' (Finset.mem_univ b')
    have hn : ‖e t b - e t b'‖ = 0 := by nlinarith [sq_nonneg ‖e t b - e t b'‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro hc
    have hdist (t : T) (b b' : B) : ‖e t b - e t b'‖ ^ 2 = 0 := by
      rw [hc t b b', sub_self, norm_zero]
      norm_num
    simp only [hdist, Finset.sum_const_zero]

theorem fiber_coherence_iff
    [Nonempty T] [Nonempty B]
    (e : T → B → E) (hunit : ∀ t b, ‖e t b‖ = 1) :
    (∑ t, ‖∑ b, e t b‖ ^ 2) /
        ((Fintype.card T : ℝ) * (Fintype.card B : ℝ) ^ 2) = 1 ↔
      ∀ t b b', e t b = e t b' := by
  have hT : (0 : ℝ) < Fintype.card T := by
    exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by
    exact_mod_cast Fintype.card_pos
  have hden : (Fintype.card T : ℝ) * (Fintype.card B : ℝ) ^ 2 ≠ 0 := by
    positivity
  rw [div_eq_one_iff_eq hden]
  have hv := normalized_fiber_variance (K := K) e hunit
  rw [← fiber_variance_zero_iff e]
  constructor <;> intro hh <;> nlinarith

theorem exact_coherence_defect
    [Nonempty T] [Nonempty B]
    (e : T → B → E) (hunit : ∀ t b, ‖e t b‖ = 1) :
    1 - (∑ t, ‖∑ b, e t b‖ ^ 2) /
        ((Fintype.card T : ℝ) * (Fintype.card B : ℝ) ^ 2) =
      (∑ t, ∑ b, ∑ b', ‖e t b - e t b'‖ ^ 2) /
        (2 * (Fintype.card T : ℝ) * (Fintype.card B : ℝ) ^ 2) := by
  have hT : (0 : ℝ) < Fintype.card T := by
    exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by
    exact_mod_cast Fintype.card_pos
  rw [normalized_fiber_variance (K := K) e hunit]
  field_simp [ne_of_gt hT, ne_of_gt hB]

#print axioms norm_sum_sq_as_double_inner
#print axioms pairwise_variance
#print axioms normalized_fiber_variance
#print axioms fiber_variance_zero_iff
#print axioms fiber_coherence_iff
#print axioms exact_coherence_defect

end LeanFiberVariance
