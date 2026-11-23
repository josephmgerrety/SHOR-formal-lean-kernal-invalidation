import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeanMeasurementNoGo

open scoped BigOperators Matrix ComplexOrder
open Matrix WithLp

variable {A L : Type*} [Fintype A] [DecidableEq A]
  [Fintype L] [DecidableEq L]

/-- A general finite quantum measurement with outcomes labeled by L. -/
structure FinitePOVM (A L : Type*) [Fintype A] [DecidableEq A]
    [Fintype L] where
  effect : L → Matrix A A ℂ
  positive : ∀ l, (effect l).PosSemidef
  complete : ∑ l, effect l = 1

/-- The Born probabilities give the correct label with certainty. -/
def PerfectlyDistinguishes (M : FinitePOVM A L)
    (psi : L → EuclideanSpace ℂ A) : Prop :=
  ∀ k l, star (ofLp (psi k)) ⬝ᵥ (M.effect l *ᵥ ofLp (psi k)) =
    if k = l then 1 else 0

theorem wrong_effect_annihilates
    (M : FinitePOVM A L) (psi : L → EuclideanSpace ℂ A)
    (hp : PerfectlyDistinguishes M psi) {k l : L} (hkl : k ≠ l) :
    M.effect l *ᵥ ofLp (psi k) = 0 := by
  apply ((M.positive l).dotProduct_mulVec_zero_iff (x := ofLp (psi k))).mp
  rw [hp k l, ite_eq_right hkl]

theorem correct_effect_fixes
    (M : FinitePOVM A L) (psi : L → EuclideanSpace ℂ A)
    (hp : PerfectlyDistinguishes M psi) (k : L) :
    M.effect k *ᵥ ofLp (psi k) = ofLp (psi k) := by
  calc
    M.effect k *ᵥ ofLp (psi k) =
        ∑ l, M.effect l *ᵥ ofLp (psi k) := by
      symm
      apply Finset.sum_eq_single k
      · intro l _ hl
        exact wrong_effect_annihilates M psi hp (Ne.symm hl)
      · intro hk
        simp at hk
    _ = (∑ l, M.effect l) *ᵥ ofLp (psi k) :=
      (Matrix.sum_mulVec Finset.univ M.effect (ofLp (psi k))).symm
    _ = ofLp (psi k) := by rw [M.complete, Matrix.one_mulVec]

theorem perfect_discrimination_implies_orthogonal
    (M : FinitePOVM A L) (psi : L → EuclideanSpace ℂ A)
    (hp : PerfectlyDistinguishes M psi) {k l : L} (hkl : k ≠ l) :
    inner ℂ (psi k) (psi l) = 0 := by
  have hk := correct_effect_fixes M psi hp k
  have hl := wrong_effect_annihilates M psi hp (Ne.symm hkl)
  have hd : star (ofLp (psi k)) ⬝ᵥ ofLp (psi l) = 0 := by
    calc
      star (ofLp (psi k)) ⬝ᵥ ofLp (psi l) =
          star (M.effect k *ᵥ ofLp (psi k)) ⬝ᵥ ofLp (psi l) := by rw [hk]
      _ = (star (ofLp (psi k)) ᵥ* (M.effect k)ᴴ) ⬝ᵥ ofLp (psi l) := by
        rw [Matrix.star_mulVec]
      _ = (star (ofLp (psi k)) ᵥ* M.effect k) ⬝ᵥ ofLp (psi l) := by
        rw [(M.positive k).isHermitian.eq]
      _ = star (ofLp (psi k)) ⬝ᵥ (M.effect k *ᵥ ofLp (psi l)) :=
        (dotProduct_mulVec _ _ _).symm
      _ = 0 := by rw [hl, dotProduct_zero]
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hd

theorem no_perfect_povm_of_nonzero_inner
    (psi : L → EuclideanSpace ℂ A) {k l : L}
    (hkl : k ≠ l) (hoverlap : inner ℂ (psi k) (psi l) ≠ 0) :
    ¬ ∃ M : FinitePOVM A L, PerfectlyDistinguishes M psi := by
  rintro ⟨M, hp⟩
  exact hoverlap (perfect_discrimination_implies_orthogonal M psi hp hkl)

/-- Arbitrary finite measurement outcomes may be grouped by their decoded label. -/
theorem decoded_measurement_gives_label_povm
    {O : Type*} [Fintype O]
    (M : FinitePOVM A O) (decode : O → L)
    (psi : L → EuclideanSpace ℂ A)
    (hp : ∀ k l,
      (∑ o, if decode o = l then
        star (ofLp (psi k)) ⬝ᵥ (M.effect o *ᵥ ofLp (psi k)) else 0) =
      if k = l then 1 else 0) :
    ∃ N : FinitePOVM A L, PerfectlyDistinguishes N psi := by
  let effect : L → Matrix A A ℂ :=
    fun l => ∑ o, if decode o = l then M.effect o else 0
  have hpos : ∀ l, (effect l).PosSemidef := by
    intro l
    apply Matrix.posSemidef_sum
    intro o _
    by_cases ho : decode o = l
    · simpa only [ho, ite_true] using M.positive o
    · simpa only [ho, ite_false] using
        (Matrix.PosSemidef.zero : (0 : Matrix A A ℂ).PosSemidef)
  have hcomplete : ∑ l, effect l = 1 := by
    dsimp [effect]
    rw [Finset.sum_comm]
    simpa using M.complete
  refine ⟨⟨effect, hpos, hcomplete⟩, ?_⟩
  intro k l
  change star (ofLp (psi k)) ⬝ᵥ (effect l *ᵥ ofLp (psi k)) = _
  have hprob :
      star (ofLp (psi k)) ⬝ᵥ (effect l *ᵥ ofLp (psi k)) =
      ∑ o, if decode o = l then
        star (ofLp (psi k)) ⬝ᵥ (M.effect o *ᵥ ofLp (psi k)) else 0 := by
    dsimp [effect]
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro o _
    by_cases ho : decode o = l <;> simp [ho]
  rw [hprob]
  exact hp k l

theorem no_perfect_decoded_povm_of_nonzero_inner
    {O : Type*} [Fintype O]
    (psi : L → EuclideanSpace ℂ A) {k l : L}
    (hkl : k ≠ l) (hoverlap : inner ℂ (psi k) (psi l) ≠ 0) :
    ¬ ∃ (M : FinitePOVM A O) (decode : O → L),
      ∀ k l,
        (∑ o, if decode o = l then
          star (ofLp (psi k)) ⬝ᵥ (M.effect o *ᵥ ofLp (psi k)) else 0) =
        if k = l then 1 else 0 := by
  rintro ⟨M, decode, hp⟩
  exact no_perfect_povm_of_nonzero_inner psi hkl hoverlap
    (decoded_measurement_gives_label_povm M decode psi hp)

#print axioms wrong_effect_annihilates
#print axioms correct_effect_fixes
#print axioms perfect_discrimination_implies_orthogonal
#print axioms no_perfect_povm_of_nonzero_inner
#print axioms decoded_measurement_gives_label_povm
#print axioms no_perfect_decoded_povm_of_nonzero_inner

end LeanMeasurementNoGo
