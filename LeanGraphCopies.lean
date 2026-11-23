import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 1000000

namespace ShorGraphCopies

open scoped BigOperators

abbrev Register (n t : ℕ) := Fin t → ZMod n
abbrev Basis (n t : ℕ) := Register n t × Register n t × Register n t

def outputWord {n t : ℕ} (k : ZMod n) (a b : Register n t) : Register n t :=
  fun i => a i - k * b i

def graphVector {𝕜 : Type*} [DivisionRing 𝕜] (n t : ℕ) (k : ZMod n) :
    EuclideanSpace 𝕜 (Basis n t) :=
  WithLp.toLp 2 (fun x =>
    if x.2.2 = outputWord k x.1 x.2.1 then ((n : 𝕜) ^ t)⁻¹ else 0)

theorem graphVector_apply {𝕜 : Type*} [DivisionRing 𝕜]
    (n t : ℕ) (k : ZMod n) (x : Basis n t) :
    graphVector (𝕜 := 𝕜) n t k x =
      if x.2.2 = outputWord k x.1 x.2.1 then ((n : 𝕜) ^ t)⁻¹ else 0 := rfl

def singleCopyAmplitude {𝕜 : Type*} [DivisionRing 𝕜]
    (n : ℕ) (k a b c : ZMod n) : 𝕜 :=
  if c = a - k * b then (n : 𝕜)⁻¹ else 0

theorem graphVector_is_independent_copy_product
    {𝕜 : Type*} [Field 𝕜] (n t : ℕ) (k : ZMod n) (x : Basis n t) :
    graphVector (𝕜 := 𝕜) n t k x =
      ∏ i : Fin t, singleCopyAmplitude (𝕜 := 𝕜) n k
        (x.1 i) (x.2.1 i) (x.2.2 i) := by
  classical
  rw [graphVector_apply]
  by_cases hx : x.2.2 = outputWord k x.1 x.2.1
  · simp [hx, singleCopyAmplitude, outputWord]
  · rw [ite_eq_right hx]
    have hcoord : ∃ i, x.2.2 i ≠ outputWord k x.1 x.2.1 i := by
      by_contra hnone
      push Not at hnone
      exact hx (funext hnone)
    obtain ⟨i, hi⟩ := hcoord
    change x.2.2 i ≠ x.1 i - k * x.2.1 i at hi
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [singleCopyAmplitude, ite_eq_right hi]

theorem graphVector_norm_sq (n t : ℕ) [NeZero n] (k : ZMod n) :
    ‖graphVector (𝕜 := ℂ) n t k‖ ^ 2 = 1 := by
  classical
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [EuclideanSpace.norm_sq_eq]
  simp [Basis, graphVector, Fintype.sum_prod_type, Register, apply_ite,
    norm_inv, norm_pow]
  field_simp

theorem graphVector_norm (n t : ℕ) [NeZero n] (k : ZMod n) :
    ‖graphVector (𝕜 := ℂ) n t k‖ = 1 := by
  have hsq := graphVector_norm_sq n t k
  have hp := norm_nonneg (graphVector (𝕜 := ℂ) n t k)
  nlinarith

theorem graphVector_inner_re_pos (n t : ℕ) [NeZero n] (k k' : ZMod n) :
    0 < (inner ℂ (graphVector (𝕜 := ℂ) n t k)
      (graphVector (𝕜 := ℂ) n t k')).re := by
  classical
  rw [PiLp.inner_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_pos'
  · intro x _
    simp only [graphVector_apply]
    split_ifs
    · simpa only [RCLike.re_eq_complex_re] using
        (inner_self_nonneg (𝕜 := ℂ) (x := ((n : ℂ) ^ t)⁻¹))
    · simp
    · simp
    · simp
  · refine ⟨(0, 0, 0), Finset.mem_univ _, ?_⟩
    have hout : outputWord k (0 : Register n t) 0 = 0 := by
      ext i
      simp [outputWord]
    have hout' : outputWord k' (0 : Register n t) 0 = 0 := by
      ext i
      simp [outputWord]
    simp only [graphVector_apply, hout, hout', ite_true]
    rw [← RCLike.re_eq_complex_re]
    apply (re_inner_self_pos (𝕜 := ℂ)).mpr
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    exact inv_ne_zero (pow_ne_zero t hn)

theorem graphVector_inner_ne_zero (n t : ℕ) [NeZero n] (k k' : ZMod n) :
    inner ℂ (graphVector (𝕜 := ℂ) n t k)
      (graphVector (𝕜 := ℂ) n t k') ≠ 0 := by
  intro heq
  have hpos := graphVector_inner_re_pos n t k k'
  rw [heq] at hpos
  norm_num at hpos

#print axioms graphVector_apply
#print axioms graphVector_is_independent_copy_product
#print axioms graphVector_norm_sq
#print axioms graphVector_norm
#print axioms graphVector_inner_re_pos
#print axioms graphVector_inner_ne_zero

end ShorGraphCopies
