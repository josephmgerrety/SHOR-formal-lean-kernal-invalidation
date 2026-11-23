import ShorWindowFamily
import Shor1994Integrated

namespace ShorWindowSourceBridge

theorem source_good_first_is_family_good_first (c cp : Nat) (z : Int) :
    Shor1994Invalidation.GoodFirst c cp z ↔
      ShorWindowFamily.GoodFirst (6006 * 16) (6006 * 17) c cp z := by
  rfl

theorem source_complete_pair_has_no_unit
    {c v cp : Nat} {z J : Int}
    (hg : Shor1994Invalidation.GoodPair 22 c v cp z J) :
    ¬ Nat.Coprime cp 32 := by
  have hf := (source_good_first_is_family_good_first c cp z).mp hg.1
  exact ShorWindowFamily.no_good_unit_of_common_factor
    (h := 6006) (N := 16) (Q := 17) (ell := 2) (R := 32)
    (by norm_num) (by norm_num) (by norm_num) (by decide)
    (by norm_num) (by norm_num) (by norm_num) hf

theorem source_claim_false_via_general_family :
    ¬ Shor1994Invalidation.PaperCompletePairUnitClaim := by
  rintro ⟨sample, hgood, hcover⟩
  obtain ⟨cp, hmem, hunit⟩ :=
    hcover 32 Shor1994Invalidation.thirty_two_is_required
  obtain ⟨c, v, z, J, hg⟩ := hgood cp hmem
  exact source_complete_pair_has_no_unit hg hunit

theorem certified_source_counterexample_via_general_family :
    Nat.Prime Shor1994Invalidation.p ∧
    orderOf (5 : ZMod 96097) = Shor1994Invalidation.n ∧
    (5 : ZMod 96097) ^ 22 = 78073 ∧
    Nat.primeFactorsList 510510 = [2, 3, 5, 7, 11, 13, 17] ∧
    Shor1994Invalidation.paperQ = Shor1994Invalidation.q ∧
    ¬ Shor1994Invalidation.PaperCompletePairUnitClaim := by
  obtain ⟨hp, ho, ht, hf, hq, _⟩ :=
    Shor1994Integrated.certified_prime_field_counterexample
  exact ⟨hp, ho, ht, hf, hq, source_claim_false_via_general_family⟩

#print axioms source_good_first_is_family_good_first
#print axioms source_complete_pair_has_no_unit
#print axioms source_claim_false_via_general_family
#print axioms certified_source_counterexample_via_general_family

end ShorWindowSourceBridge
