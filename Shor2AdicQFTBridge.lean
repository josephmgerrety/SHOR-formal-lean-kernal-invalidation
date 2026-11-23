import Shor2AdicTorsionHierarchy

namespace Shor2AdicQFTBridge

open scoped BigOperators
open Shor2AdicTorsionHierarchy

/-- Powers of a certified root agree after reducing the exponent. -/
theorem root_power_reduce {R : Type*} [Monoid R]
    (root : R) (q e : ℕ) (hroot : root ^ q = 1) :
    root ^ (e % q) = root ^ e := by
  calc
    root ^ (e % q) = root ^ (e % q + q * (e / q)) := by
      simp only [pow_add, pow_mul, hroot, one_pow, mul_one]
    _ = root ^ e := by rw [Nat.mod_add_div]

/-- The explicit positive-sign QFT phase is a primitive 128th root. -/
theorem explicit_qft_128_root_primitive :
    IsPrimitiveRoot
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 128)) 128 := by
  exact Complex.isPrimitiveRoot_exp 128 (by norm_num)

theorem explicit_qft_128_root_pow :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 128)) ^ 128 = 1 :=
  explicit_qft_128_root_primitive.pow_eq_one

theorem explicit_qft_128_root_half_period :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 128)) ^ 64 = -1 := by
  rw [← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have harg : (64 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 128) =
      (Real.pi : ℂ) * Complex.I := by ring
  rw [harg]
  exact Complex.exp_pi_mul_I

/-- The numerical congruences imply zero numerators after certifying the phase. -/
theorem certified_root_zero_columns {R : Type*} [CommRing R]
    (root : R) (hroot : root ^ 128 = 1) (hhalf : root ^ 64 = -1)
    (u t : ℕ) :
    rawPaddedFiberSum 116 22 u 32 t root = 0 ∧
    rawPaddedFiberSum 116 22 u 96 t root = 0 ∧
    rawPaddedFiberSum 100 22 u 32 t root = 0 ∧
    rawPaddedFiberSum 100 22 u 96 t root = 0 := by
  have hneg (e : ℕ) (he : e % 128 = 64) : root ^ e = -1 := by
    rw [← root_power_reduce root 128 e hroot, he]
    exact hhalf
  exact ⟨zero_column_of_half_period_neg_one 58 11 u 32 t root
      (hneg (32 * 58) (by decide)),
    zero_column_of_half_period_neg_one 58 11 u 96 t root
      (hneg (96 * 58) (by decide)),
    zero_column_of_half_period_neg_one 50 11 u 32 t root
      (hneg (32 * 50) (by decide)),
    zero_column_of_half_period_neg_one 50 11 u 96 t root
      (hneg (96 * 50) (by decide))⟩

/-- The two columns vanish at the actual complex QFT phase, for every u and t. -/
theorem actual_qft_zero_columns (u t : ℕ) :
    let root : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 128)
    rawPaddedFiberSum 116 22 u 32 t root = 0 ∧
    rawPaddedFiberSum 116 22 u 96 t root = 0 ∧
    rawPaddedFiberSum 100 22 u 32 t root = 0 ∧
    rawPaddedFiberSum 100 22 u 96 t root = 0 := by
  exact certified_root_zero_columns _ explicit_qft_128_root_pow
    explicit_qft_128_root_half_period u t

/-- Each zero column also has zero normalized Born mass after summing fibers. -/
theorem actual_qft_zero_column_born_mass (u : ℕ) :
    let root : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 128)
    (∑ t ∈ Finset.range 116,
      Complex.normSq (rawPaddedFiberSum 116 22 u 32 t root / (116 * 128))) = 0 ∧
    (∑ t ∈ Finset.range 116,
      Complex.normSq (rawPaddedFiberSum 116 22 u 96 t root / (116 * 128))) = 0 ∧
    (∑ t ∈ Finset.range 100,
      Complex.normSq (rawPaddedFiberSum 100 22 u 32 t root / (100 * 128))) = 0 ∧
    (∑ t ∈ Finset.range 100,
      Complex.normSq (rawPaddedFiberSum 100 22 u 96 t root / (100 * 128))) = 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro t _
    rw [(actual_qft_zero_columns u t).1]
    simp
  · apply Finset.sum_eq_zero
    intro t _
    rw [(actual_qft_zero_columns u t).2.1]
    simp
  · apply Finset.sum_eq_zero
    intro t _
    rw [(actual_qft_zero_columns u t).2.2.1]
    simp
  · apply Finset.sum_eq_zero
    intro t _
    rw [(actual_qft_zero_columns u t).2.2.2]
    simp

/-- This includes both the q/12 first-frequency test and the phase inequality. -/
abbrev GoodPair1997 (n q k c v cp : ℕ) (z j : ℤ) : Prop :=
  GoodFirst1997 n q c cp z ∧ v < q ∧
  2 * |(n : ℤ) * ((k : ℤ) * c + v - j * q) - (k : ℤ) * z| ≤ n

/-- The three displayed table pairs meet both explicit inequalities. -/
theorem shor_100_complete_table_rows :
    GoodPair1997 100 128 22 9 59 7 4 2 ∧
    GoodPair1997 100 128 22 18 118 14 8 4 ∧
    GoodPair1997 100 128 22 41 123 32 4 8 := by
  norm_num [GoodPair1997, GoodFirst1997]

/-- The negative-step geometric filter need not vanish for odd torsion length. -/
theorem odd_torsion_filter_counterexample :
    ((-1 : ℤ) ^ 1 = -1) ∧
    (∑ j ∈ Finset.range 3, (-1 : ℤ) ^ j) = 1 := by
  norm_num [Finset.sum_range_succ]

#print axioms root_power_reduce
#print axioms explicit_qft_128_root_primitive
#print axioms explicit_qft_128_root_pow
#print axioms explicit_qft_128_root_half_period
#print axioms certified_root_zero_columns
#print axioms actual_qft_zero_columns
#print axioms actual_qft_zero_column_born_mass
#print axioms shor_100_complete_table_rows
#print axioms odd_torsion_filter_counterexample

end Shor2AdicQFTBridge
