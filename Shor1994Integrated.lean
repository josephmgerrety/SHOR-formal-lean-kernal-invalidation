import Shor1994Invalidation
import ShorGeneratorCertificate
import ShorPrimorialCertificate

namespace Shor1994Integrated

theorem certified_prime_field_counterexample :
    Nat.Prime Shor1994Invalidation.p ∧
    orderOf (5 : ZMod 96097) = Shor1994Invalidation.n ∧
    (5 : ZMod 96097) ^ 22 = 78073 ∧
    Nat.primeFactorsList 510510 = [2, 3, 5, 7, 11, 13, 17] ∧
    Shor1994Invalidation.paperQ = Shor1994Invalidation.q ∧
    ¬ Shor1994Invalidation.PaperCompletePairUnitClaim := by
  obtain ⟨_, _, _, _, _, hq⟩ :=
    Shor1994Invalidation.paper_modulus_certificate
  exact ⟨Shor1994Invalidation.p_is_prime,
    by simpa [Shor1994Invalidation.n] using ShorGenerator.generator_order,
    ShorGenerator.fifth_power_target,
    ShorPrimorial.prime_factors,
    hq,
    Shor1994Invalidation.paper_complete_pair_unit_claim_false⟩

#check Shor1994Invalidation.complete_good_pair_iff_indexed
#check Shor1994Invalidation.actual_qft_conditional_bound_false
#print axioms certified_prime_field_counterexample

end Shor1994Integrated
