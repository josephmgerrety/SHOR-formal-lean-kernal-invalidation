import Shor1994Integrated
import ShorWindowFamily
import ShorWindowSourceBridge
import LeanFiberFourier
import LeanFourierNormalization
import LeanFiniteCopyNoGo
import Shor2AdicTorsionHierarchy

namespace Shor2AdicMasterBridge

open scoped BigOperators
open Shor1994Invalidation
open ShorWindowFamily
open LeanFiberFourier
open ShorFiniteCopyNoGo
open Shor2AdicTorsionHierarchy

/-!
===========================================================================
1. EXACT 1 - 1/2^r WORKSPACE COHERENCE DEFECT IN `LeanFiberFourier`
===========================================================================
The hypothesis hvar specifies total pairwise fiber variance
`2 * n^3 * (1 - 1/2^r)`. The exact Fourier defect identity then gives
line probability `1/2^r` and off-line probability `1 - 1/2^r`.
The separate residue-workspace extension derives the variance from
balanced labels and their squared-distance law.
-/

theorem two_adic_workspace_line_defect_and_survival
    {n : ℕ} [NeZero n]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : ZMod n → ZMod n → E) (k : ZMod n) (r : ℕ)
    (hunit : ∀ a b, ‖e a b‖ = 1)
    (hvar :
      (∑ t : ZMod n, ∑ b : ZMod n, ∑ b' : ZMod n,
        ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2) =
      2 * (n : ℝ) ^ 3 * (1 - 1 / (2 : ℝ) ^ r)) :
    1 - (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      1 - 1 / (2 : ℝ) ^ r ∧
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      1 / (2 : ℝ) ^ r := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hdef := exact_fourier_line_defect e k hunit
  rw [hvar] at hdef
  have hsimp :
      2 * (n : ℝ) ^ 3 * (1 - 1 / (2 : ℝ) ^ r) / (2 * (n : ℝ) ^ 3) =
        1 - 1 / (2 : ℝ) ^ r := by
    field_simp [hn]
  rw [hsimp] at hdef
  constructor
  · exact hdef
  · linarith

/-!
===========================================================================
2. 1994 COUNTEREXAMPLE 16-COSET & 32-COSET BLINDNESS BRIDGE
===========================================================================
For the certified prime field `p = 96097` (`n = 96096 = 16 * 6006`,
`q = 102102 = 17 * 6006`), every good pair `(c, v, cp, z, j)` has `cp = 16 * idx`,
so its rounding congruence `k * cp + e = n * j` is simultaneously satisfied
by all 16 keys `k + 6006 * s`. For the 3003 even good pairs (`32 ∣ cp`),
the rounding congruence is simultaneously satisfied by all 32 keys `k + 3003 * s`.
-/

theorem source_good_pair_sixteen_coset_blindness
    {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j) (s : ℤ) :
    ∃ J_s : ℤ,
      ((k : ℤ) + s * 6006) * (cp : ℤ) +
        reconstructedInteger k cp j = (n : ℤ) * J_s := by
  obtain ⟨_, hcong⟩ := paper_rounding_and_congruence hg
  obtain ⟨idx, _, _, hcp, _⟩ := Shor1994Invalidation.every_good_coefficient_shape hg.1
  refine ⟨j + s * (idx : ℤ), ?_⟩
  have hcpZ : (cp : ℤ) = 16 * (idx : ℤ) := by exact_mod_cast hcp
  have hnZ : (n : ℤ) = 16 * 6006 := by norm_num [n]
  rw [hcpZ, hnZ] at hcong ⊢
  exact rounded_congruence_satisfied_by_entire_coset hcong s

theorem source_even_good_pair_thirty_two_coset_blindness
    {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j)
    (hdiv : 32 ∣ cp) (s : ℤ) :
    ∃ J_s : ℤ,
      ((k : ℤ) + s * 3003) * (cp : ℤ) +
        reconstructedInteger k cp j = (n : ℤ) * J_s := by
  obtain ⟨_, hcong⟩ := paper_rounding_and_congruence hg
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨j + s * (r : ℤ), ?_⟩
  have hcpZ : (cp : ℤ) = 32 * (r : ℤ) := by exact_mod_cast hr
  have hnZ : (n : ℤ) = 32 * 3003 := by norm_num [n]
  rw [hcpZ, hnZ] at hcong ⊢
  exact rounded_congruence_satisfied_by_entire_coset hcong s

/-!
===========================================================================
3. MASTER SYNTHESIS THEOREM: THE FOUR INTERLOCKING OBSTRUCTIONS
===========================================================================
This conjunction contains the characteristic-two matrix identity,
Boolean sign periodicity, the binary-control congruence, four numerical
phase residues, the certified 1994 input and unit-claim negation,
16-coset congruence invariance, and the finite-copy zero-error POVM theorem.
Other results in the imported modules retain their own hypotheses and
are audited separately in AxiomAudit and the external proof export.
-/

theorem four_interlocking_shor_obstructions :
    -- (I) The characteristic-two matrix identity and sign periodicity
    (∀ i k : Fin 2,
      (∑ j : Fin 2, hadamardMod2 i j * hadamardMod2 j k) = 0) ∧
    (∀ u a : ℕ,
      booleanSignCharacter (u + 2) a = booleanSignCharacter u a) ∧
    -- (II) 2-adic binary control bottleneck & universal zero-column frequencies
    (∀ r m j k s : ℕ, r ≤ j →
      (2 ^ j * (k + s * m)) % (2 ^ r * m) = (2 ^ j * k) % (2 ^ r * m)) ∧
    ((32 * 58) % 128 = 64 ∧ (96 * 58) % 128 = 64 ∧
     (32 * 50) % 128 = 64 ∧ (96 * 50) % 128 = 64) ∧
    -- (III) Certified p = 96097 input, unit-claim negation, and 16-coset invariance
    (Nat.Prime p ∧
     orderOf (5 : ZMod 96097) = n ∧
     paperQ = q ∧
     ¬ PaperCompletePairUnitClaim) ∧
    (∀ {k c v cp : ℕ} {z j : ℤ},
      GoodPair k c v cp z j → ∀ s : ℤ,
        ∃ J_s : ℤ,
          ((k : ℤ) + s * 6006) * (cp : ℤ) +
            reconstructedInteger k cp j = (n : ℤ) * J_s) ∧
    -- (IV) Universal finite-copy zero-error POVM no-go for all N_ord > 1 and copy counts t
    (∀ N_ord t : ℕ, ∀ hN : 1 < N_ord,
      letI : NeZero N_ord := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hN)⟩
      ¬ ∃ M : LeanMeasurementNoGo.FinitePOVM (ShorGraphCopies.Basis N_ord t) (ZMod N_ord),
        LeanMeasurementNoGo.PerfectlyDistinguishes M
          (ShorGraphCopies.graphVector (𝕜 := ℂ) N_ord t)) := by
  refine ⟨hadamard_mod2_sq_eq_zero,
    boolean_sign_character_period_two,
    binary_control_stage_invariance,
    elliptic_116_and_shor_100_zero_column_frequencies,
    ?_,
    @source_good_pair_sixteen_coset_blindness,
    ?_⟩
  · obtain ⟨hp, ho, _, _, hq, hfalse⟩ :=
      Shor1994Integrated.certified_prime_field_counterexample
    exact ⟨hp, ho, hq, hfalse⟩
  · intro N_ord t hN
    exact (every_group_order_and_finite_copy_count N_ord t hN).2

#print axioms two_adic_workspace_line_defect_and_survival
#print axioms source_good_pair_sixteen_coset_blindness
#print axioms source_even_good_pair_thirty_two_coset_blindness
#print axioms four_interlocking_shor_obstructions

end Shor2AdicMasterBridge
