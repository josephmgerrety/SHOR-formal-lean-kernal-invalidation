import Shor1994Integrated

namespace ShorArithmeticStrengthening

open Shor1994Invalidation

/-- The common kernel of all good rounded-coefficient congruences. -/
def GoodCoefficientKernel (delta : ℤ) : Prop :=
  ∀ c cp : ℕ, ∀ z : ℤ, GoodFirst c cp z →
    (n : ℤ) ∣ delta * (cp : ℤ)

/-- Every good coefficient is a multiple of 16, and the good coefficient
    16 itself fixes the common kernel exactly. -/
theorem all_good_congruences_exact_kernel (delta : ℤ) :
    GoodCoefficientKernel delta ↔ (6006 : ℤ) ∣ delta := by
  constructor
  · intro hall
    have hgood : GoodFirst 17 16 0 := by
      norm_num [GoodFirst, n, q]
    obtain ⟨w, hw⟩ := hall 17 16 0 hgood
    refine ⟨w, ?_⟩
    norm_num [n] at hw
    omega
  · rintro ⟨w, hw⟩ c cp z hg
    obtain ⟨idx, _, _, hcp, _⟩ := every_good_coefficient_shape hg
    refine ⟨w * (idx : ℤ), ?_⟩
    rw [hw, hcp]
    norm_num [n]
    ring

/-- Sixteen distinct representatives of the common congruence ambiguity
    for the certified scalar 22. -/
theorem sixteen_distinct_common_candidates :
    ((Finset.range 16).image (fun s => (22 + s * 6006) % 96096)).card = 16 := by
  decide

/-- The power-of-two modulus required in the 1997 construction for this
    prime has reduced modulus 4096, outside the Q < 12 collapse range. -/
theorem power_two_modulus_for_96097 :
    (2 : ℕ) ^ 17 = 131072 ∧
    p < 2 ^ 17 ∧ 2 ^ 17 < 2 * p ∧
    Nat.gcd n (2 ^ 17) = 32 ∧
    (2 : ℕ) ^ 17 / Nat.gcd n (2 ^ 17) = 4096 ∧
    ¬ (4096 : ℕ) < 12 := by
  norm_num [p, n]

#print axioms all_good_congruences_exact_kernel
#print axioms sixteen_distinct_common_candidates
#print axioms power_two_modulus_for_96097

end ShorArithmeticStrengthening
