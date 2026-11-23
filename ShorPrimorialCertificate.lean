import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace ShorPrimorial

theorem prime_product :
    2 * 3 * 5 * 7 * 11 * 13 * 17 = 510510 := by
  norm_num

theorem prime_factors :
    Nat.primeFactorsList 510510 = [2, 3, 5, 7, 11, 13, 17] := by
  have hperm :
      List.Perm [2, 3, 5, 7, 11, 13, 17]
        (Nat.primeFactorsList 510510) := by
    apply Nat.primeFactorsList_unique (by norm_num)
    intro r hr
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num
  have hsorted : List.SortedLE [2, 3, 5, 7, 11, 13, 17] := by
    decide
  exact (List.Perm.eq_of_sortedLE hsorted
    (Nat.primeFactorsList_sorted 510510) hperm).symm

theorem quotient_by_five :
    510510 / 5 = 102102 := by
  norm_num

theorem above_p :
    96097 < 510510 / 5 := by
  norm_num

theorem quotient_by_seven :
    510510 / 7 = 72930 := by
  norm_num

theorem below_p :
    510510 / 7 < 96097 := by
  norm_num

theorem no_larger_removal (r : Nat)
    (hr : r ∈ Nat.primeFactorsList 510510)
    (hgt : 5 < r) :
    510510 / r < 96097 := by
  rw [prime_factors] at hr
  simp at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at *

theorem five_is_largest :
    ∀ r ∈ Nat.primeFactorsList 510510,
      96097 < 510510 / r → r ≤ 5 := by
  intro r hr hq
  by_contra hle
  have hgt : 5 < r := by omega
  have hsmall := no_larger_removal r hr hgt
  omega

#print axioms prime_factors
#print axioms five_is_largest

end ShorPrimorial
