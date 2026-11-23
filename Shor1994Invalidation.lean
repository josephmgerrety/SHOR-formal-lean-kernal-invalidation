import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Init.Omega

/-!
The source equations are from the original 1994 paper, printed pp. 8--10:
the `n × n` arithmetic graph of (7.26), the centered residue and the
`q/20` good window of (7.35), and the phase inequality (7.34).
Here n = p - 1 = 96096 and q = 102102.
-/

namespace Shor1994Invalidation

open scoped BigOperators

def p : ℕ := 96097
def n : ℕ := 96096
def q : ℕ := 102102
def h : ℕ := 6006

theorem parameter_arithmetic :
    n = p - 1 ∧ n = 16 * h ∧ q = 17 * h ∧ p < q ∧ q < 2 * p := by
  norm_num [p, n, q, h]

theorem p_is_prime : Nat.Prime p := by
  norm_num [p]

def primePrefix : ℕ := 2 * 3 * 5 * 7 * 11 * 13
def primeProduct : ℕ := primePrefix * 17
def candidateFactors : List ℕ := [2, 3, 5, 7, 11, 13, 17]

def selectedFactor : ℕ :=
  (candidateFactors.filter fun r => p < primeProduct / r).foldl max 0

def paperQ : ℕ :=
  if 2 * p < primeProduct then primeProduct / selectedFactor else primeProduct

theorem paper_modulus_certificate :
    primePrefix = 30030 ∧
    primePrefix < p ∧
    primeProduct = 510510 ∧
    2 * p < primeProduct ∧
    selectedFactor = 5 ∧
    paperQ = q := by
  decide

theorem prime_prefix_complete :
    (∀ r ∈ Finset.range 18,
      (Nat.Prime r ↔ r ∈ candidateFactors)) ∧
    Nat.Prime 17 := by
  decide

theorem prime_prefix_contains_all_primes_through_seventeen (r : ℕ)
    (hr : r ≤ 17) :
    Nat.Prime r ↔ r ∈ candidateFactors :=
  prime_prefix_complete.1 r (Finset.mem_range.mpr (by omega))

theorem no_larger_removable_factor (r : ℕ) (hr : 5 < r) :
    ¬ p < primeProduct / r := by
  intro hquotient
  have hrpos : 0 < r := by omega
  have hmul : (p + 1) * r ≤ primeProduct :=
    (Nat.le_div_iff_mul_le hrpos).mp (by omega)
  norm_num [p, primeProduct, primePrefix] at hmul
  omega

/- `z` is the centered residue of `n*c` modulo `q`.
   `cp` is the paper's coefficient c-prime, defined by n*c = q*cp + z. -/
def GoodFirst (c cp : ℕ) (z : ℤ) : Prop :=
  c < q ∧
  cp < n ∧
  (n : ℤ) * (c : ℤ) = (q : ℤ) * (cp : ℤ) + z ∧
  -(q : ℤ) < 2 * z ∧
  2 * z ≤ (q : ℤ) ∧
  20 * |z| ≤ (q : ℤ)

/- `w` is n times the residual in (7.34). The pair predicate retains the
   separate frequency v and the phase-grid integer j. -/
def GoodPair (k c v cp : ℕ) (z j : ℤ) : Prop :=
  GoodFirst c cp z ∧
  v < q ∧
  2 * |(n : ℤ) * ((k : ℤ) * (c : ℤ) + (v : ℤ) - j * (q : ℤ))
        - (k : ℤ) * z| ≤ (n : ℤ)

theorem good_pair_has_good_first {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j) : GoodFirst c cp z := hg.1

/- Eqs. (7.40)--(7.41): the same accepted pair determines an integer e.
   The equality n*v-q*e=w is derived from the two original equations;
   2*|w|≤n<q makes e the unique nearest integer to n*v/q. -/
def reconstructedInteger (k cp : ℕ) (j : ℤ) : ℤ :=
  (n : ℤ) * j - (k : ℤ) * (cp : ℤ)

theorem paper_rounding_identity {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j) :
    (n : ℤ) * (v : ℤ) - (q : ℤ) * reconstructedInteger k cp j =
      (n : ℤ) * ((k : ℤ) * (c : ℤ) + (v : ℤ) - j * (q : ℤ)) -
        (k : ℤ) * z := by
  obtain ⟨_, _, heq, _, _, _⟩ := hg.1
  unfold reconstructedInteger
  calc
    (n : ℤ) * (v : ℤ) - (q : ℤ) * ((n : ℤ) * j - (k : ℤ) * (cp : ℤ)) =
      (n : ℤ) * ((k : ℤ) * (c : ℤ) + (v : ℤ) - j * (q : ℤ)) -
        (k : ℤ) * ((n : ℤ) * (c : ℤ) - (q : ℤ) * (cp : ℤ)) := by ring
    _ = (n : ℤ) * ((k : ℤ) * (c : ℤ) + (v : ℤ) - j * (q : ℤ)) -
        (k : ℤ) * z := by rw [heq]; ring

theorem paper_rounding_and_congruence {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j) :
    2 * |(n : ℤ) * (v : ℤ) - (q : ℤ) * reconstructedInteger k cp j| <
      (q : ℤ) ∧
    (k : ℤ) * (cp : ℤ) + reconstructedInteger k cp j = (n : ℤ) * j := by
  constructor
  · rw [paper_rounding_identity hg]
    have hwindow := hg.2.2
    norm_num [n, q] at hwindow ⊢
    omega
  · unfold reconstructedInteger
    ring

theorem nearest_integer_unique {v : ℕ} {e₁ e₂ : ℤ}
    (h₁ : 2 * |(n : ℤ) * (v : ℤ) - (q : ℤ) * e₁| < (q : ℤ))
    (h₂ : 2 * |(n : ℤ) * (v : ℤ) - (q : ℤ) * e₂| < (q : ℤ)) :
    e₁ = e₂ := by
  have hb₁ : |(n : ℤ) * (v : ℤ) - (q : ℤ) * e₁| ≤ 51050 := by
    norm_num [q] at h₁ ⊢
    omega
  have hb₂ : |(n : ℤ) * (v : ℤ) - (q : ℤ) * e₂| ≤ 51050 := by
    norm_num [q] at h₂ ⊢
    omega
  have hbounds₁ := abs_le.mp hb₁
  have hbounds₂ := abs_le.mp hb₂
  norm_num [n, q] at hbounds₁ hbounds₂ ⊢
  omega

theorem every_good_residue_zero {c cp : ℕ} {z : ℤ}
    (hg : GoodFirst c cp z) : z = 0 := by
  rcases hg with ⟨_, _, heq, _, _, hwindow⟩
  have hsmall : |z| ≤ (5105 : ℤ) := by
    norm_num [q] at hwindow ⊢
    omega
  have hbounds := abs_le.mp hsmall
  have hmultiple :
      z = 6006 * (16 * (c : ℤ) - 17 * (cp : ℤ)) := by
    norm_num [n, q] at heq
    omega
  omega

theorem every_good_coefficient_shape {c cp : ℕ} {z : ℤ}
    (hg : GoodFirst c cp z) :
    ∃ j : ℕ, j < h ∧ c = 17 * j ∧ cp = 16 * j ∧ z = 0 := by
  have hz : z = 0 := every_good_residue_zero hg
  rcases hg with ⟨hc, hcp, heq, _, _, _⟩
  have hrel : 16 * c = 17 * cp := by
    norm_num [n, q] at heq
    omega
  have hdiv : 16 ∣ cp := by omega
  rcases hdiv with ⟨j, hj⟩
  refine ⟨j, ?_, ?_, ?_, hz⟩
  · norm_num [n, h] at hcp ⊢
    omega
  · omega
  · omega

theorem each_index_is_good (j : ℕ) (hj : j < h) :
    GoodFirst (17 * j) (16 * j) 0 := by
  unfold GoodFirst
  norm_num [n, q, h] at hj ⊢
  omega

theorem good_first_iff_exact_lattice {c cp : ℕ} {z : ℤ} :
    GoodFirst c cp z ↔
      ∃ j : ℕ, j < h ∧ c = 17 * j ∧ cp = 16 * j ∧ z = 0 := by
  constructor
  · exact every_good_coefficient_shape
  · rintro ⟨j, hj, rfl, rfl, rfl⟩
    exact each_index_is_good j hj

def goodCoefficientSet : Finset ℕ :=
  (Finset.range h).image (fun j => 16 * j)

theorem good_coefficient_membership (cp : ℕ) :
    cp ∈ goodCoefficientSet ↔
      ∃ c : ℕ, ∃ z : ℤ, GoodFirst c cp z := by
  constructor
  · intro hmem
    obtain ⟨j, hj, hcp⟩ := Finset.mem_image.mp hmem
    refine ⟨17 * j, 0, ?_⟩
    rw [← hcp]
    exact each_index_is_good j (Finset.mem_range.mp hj)
  · rintro ⟨c, z, hg⟩
    obtain ⟨j, hj, _, hcp, _⟩ := every_good_coefficient_shape hg
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr hj, hcp.symm⟩

theorem good_coefficient_count : goodCoefficientSet.card = 6006 := by
  have hinj : Function.Injective (fun j : ℕ => 16 * j) := by
    intro a b hab
    change 16 * a = 16 * b at hab
    omega
  simpa [goodCoefficientSet, h] using
    (Finset.card_image_of_injective (Finset.range h) hinj)

def divisibleGoodCoefficients : Finset ℕ :=
  goodCoefficientSet.filter (fun cp => 32 ∣ cp)

theorem divisible_coefficient_set_exact :
    divisibleGoodCoefficients =
      (Finset.range 3003).image (fun r => 32 * r) := by
  ext cp
  constructor
  · intro hmem
    obtain ⟨hcp, h32⟩ := Finset.mem_filter.mp hmem
    obtain ⟨j, hj, hcpj⟩ := Finset.mem_image.mp hcp
    have hj2 : 2 ∣ j := by
      rw [← hcpj] at h32
      omega
    obtain ⟨r, hr⟩ := hj2
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_range.mpr ?_, ?_⟩
    · have hjbound : j < h := Finset.mem_range.mp hj
      dsimp [h] at hjbound
      omega
    · omega
  · intro hmem
    obtain ⟨r, hr, hcp⟩ := Finset.mem_image.mp hmem
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨2 * r, Finset.mem_range.mpr ?_, ?_⟩
      · have hrbound : r < 3003 := Finset.mem_range.mp hr
        dsimp [h]
        omega
      · omega
    · rw [← hcp]
      exact dvd_mul_right 32 r

theorem divisible_good_coefficient_count :
    divisibleGoodCoefficients.card = 3003 := by
  rw [divisible_coefficient_set_exact]
  have hinj : Function.Injective (fun r : ℕ => 32 * r) := by
    intro a b hab
    change 32 * a = 32 * b at hab
    omega
  simpa using
    (Finset.card_image_of_injective (Finset.range 3003) hinj)

theorem printed_ten_over_thirty_two_bound_false :
    (10 : ℚ) / 32 <
      (divisibleGoodCoefficients.card : ℚ) /
        (goodCoefficientSet.card : ℚ) := by
  rw [divisible_good_coefficient_count, good_coefficient_count]
  norm_num

theorem no_good_coefficient_coprime_32 {c cp : ℕ} {z : ℤ}
    (hg : GoodFirst c cp z) : ¬ Nat.Coprime cp 32 := by
  intro hcop
  obtain ⟨j, _, _, hcp, _⟩ := every_good_coefficient_shape hg
  have h16 : 16 ∣ cp := by
    rw [hcp]
    exact dvd_mul_right 16 j
  have h2 : 2 ∣ cp := (by norm_num : 2 ∣ (16 : ℕ)).trans h16
  have h2g : 2 ∣ Nat.gcd cp 32 := Nat.dvd_gcd h2 (by norm_num)
  have hgc : Nat.gcd cp 32 = 1 := hcop
  rw [hgc] at h2g
  norm_num at h2g

/- Prime powers R > 20 dividing n are exactly the powers at issue in the
   page 10 recovery sentence. It suffices to instantiate this predicate at
   R = 2^5 = 32. -/
def LargePrimePowerDivisor (R : ℕ) : Prop :=
  ∃ ℓ e : ℕ, Nat.Prime ℓ ∧ 0 < e ∧ R = ℓ ^ e ∧ 20 < R ∧ R ∣ n

def PaperUnitExistenceClaim : Prop :=
  ∃ sample : Finset ℕ,
    (∀ cp ∈ sample, ∃ c : ℕ, ∃ z : ℤ, GoodFirst c cp z) ∧
    (∀ R : ℕ, LargePrimePowerDivisor R →
      ∃ cp ∈ sample, Nat.Coprime cp R)

theorem thirty_two_is_required : LargePrimePowerDivisor 32 := by
  refine ⟨2, 5, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num [n]

theorem paper_unit_existence_claim_false : ¬ PaperUnitExistenceClaim := by
  intro hclaim
  obtain ⟨sample, hgood, hcover⟩ := hclaim
  obtain ⟨cp, hmem, hunit⟩ := hcover 32 thirty_two_is_required
  obtain ⟨c, z, hg⟩ := hgood cp hmem
  exact no_good_coefficient_coprime_32 hg hunit

theorem no_good_pair_unit_32 {k c v cp : ℕ} {z j : ℤ}
    (hg : GoodPair k c v cp z j) : ¬ Nat.Coprime cp 32 :=
  no_good_coefficient_coprime_32 hg.1

def PaperCompletePairUnitClaim : Prop :=
  ∃ sample : Finset ℕ,
    (∀ cp ∈ sample,
      ∃ c v : ℕ, ∃ z j : ℤ, GoodPair 22 c v cp z j) ∧
    (∀ R : ℕ, LargePrimePowerDivisor R →
      ∃ cp ∈ sample, Nat.Coprime cp R)

theorem paper_complete_pair_unit_claim_false :
    ¬ PaperCompletePairUnitClaim := by
  intro hclaim
  obtain ⟨sample, hgood, hcover⟩ := hclaim
  obtain ⟨cp, hmem, hunit⟩ := hcover 32 thirty_two_is_required
  obtain ⟨c, v, z, j, hg⟩ := hgood cp hmem
  exact no_good_pair_unit_32 hg hunit

/- A concrete accepted pair for the nonzero scalar k = 22. -/
theorem explicit_complete_good_pair : GoodPair 22 17 101728 16 0 1 := by
  norm_num [GoodPair, GoodFirst, n, q]

theorem explicit_decoded_relation :
    96096 * (101728 : ℤ) - 102102 * (95744 : ℤ) = 0 ∧
    22 * (16 : ℤ) + 95744 = 96096 := by
  norm_num

/- Eq. (7.26): the first two registers run through [0,N)², and the third
   contains g^a x^(-b), represented by a-kb modulo N when x=g^k.
   Eq. (7.29) parameterizes every group-output fiber by b. -/
def paperGraphOutput (N k a b : ℕ) : ℕ :=
  (a + N - (k * b) % N) % N

def paperGraphFiber (N k t b : ℕ) : ℕ := (t + k * b) % N

theorem source_graph_fiber_iff {a b t : ℕ}
    (ha : a < n) (ht : t < n) :
    paperGraphOutput n 22 a b = t ↔ a = paperGraphFiber n 22 t b := by
  unfold paperGraphOutput paperGraphFiber
  norm_num [n] at ha ht ⊢
  omega

/- Eq. (7.28) before reindexing: the finite double character sum at the
   ordered Fourier frequencies (c,v) and the group-output exponent t.
   The amplitude is this numerator divided by N*Q. -/
def paperFourierNumerator {R : Type*} [CommSemiring R]
    (N Q k c v t : ℕ) (root : R) : R :=
  ∑ b ∈ Finset.range N,
    ∑ a ∈ Finset.range N,
      if paperGraphOutput N k a b = t then
        root ^ ((c * a + v * b) % Q) else 0

/- This is the source's literal Eq. (7.28) character sum, before reduction
   of the Fourier exponent modulo Q. -/
def paperFourierRawNumerator {R : Type*} [CommSemiring R]
    (N _Q k c v t : ℕ) (root : R) : R :=
  ∑ b ∈ Finset.range N,
    ∑ a ∈ Finset.range N,
      if paperGraphOutput N k a b = t then
        root ^ (c * a + v * b) else 0

theorem power_reduction_at_root_of_unity {R : Type*} [Monoid R]
    (Q : ℕ) (root : R) (hroot : root ^ Q = 1) (e : ℕ) :
    root ^ (e % Q) = root ^ e := by
  have he : e % Q + Q * (e / Q) = e := Nat.mod_add_div e Q
  calc
    root ^ (e % Q) = root ^ (e % Q + Q * (e / Q)) := by
      simp [pow_add, pow_mul, hroot]
    _ = root ^ e := by rw [he]

theorem raw_fourier_equals_reduced {R : Type*} [CommSemiring R]
    (N Q k c v t : ℕ) (root : R) (hroot : root ^ Q = 1) :
    paperFourierRawNumerator N Q k c v t root =
      paperFourierNumerator N Q k c v t root := by
  unfold paperFourierRawNumerator paperFourierNumerator
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : paperGraphOutput N k a b = t
  · simp only [hs, ite_true]
    exact (power_reduction_at_root_of_unity Q root hroot _).symm
  · simp [hs]

theorem source_fourier_fiber_reindex {R : Type*} [CommSemiring R]
    (c v t : ℕ) (root : R) (ht : t < n) :
    paperFourierNumerator n q 22 c v t root =
      ∑ b ∈ Finset.range n,
        root ^ ((c * paperGraphFiber n 22 t b + v * b) % q) := by
  unfold paperFourierNumerator
  apply Finset.sum_congr rfl
  intro b _
  have hf : paperGraphFiber n 22 t b < n := Nat.mod_lt _ (by norm_num [n])
  calc
    (∑ a ∈ Finset.range n,
        if paperGraphOutput n 22 a b = t then
          root ^ ((c * a + v * b) % q) else 0) =
      ∑ a ∈ Finset.range n,
        if a = paperGraphFiber n 22 t b then
          root ^ ((c * a + v * b) % q) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hcond : a = paperGraphFiber n 22 t b
        · subst a
          have hsource :
              paperGraphOutput n 22 (paperGraphFiber n 22 t b) b = t :=
            (source_graph_fiber_iff hf ht).2 rfl
          simp only [hsource, ite_true]
        · have hsource : paperGraphOutput n 22 a b ≠ t := by
            intro hh
            exact hcond ((source_graph_fiber_iff (Finset.mem_range.mp ha) ht).1 hh)
          simp [hcond, hsource]
    _ = root ^ ((c * paperGraphFiber n 22 t b + v * b) % q) := by
      simp only [Finset.sum_ite_eq', Finset.mem_range, hf, ↓reduceIte]

/- In the concrete source graph, a=t+22b (mod n). The following theorem
   keeps the full carry generated by reduction modulo n. -/
def graphFirstExponent (t b : ℕ) : ℕ := (t + 22 * b) % n

theorem source_graph_fiber (t b : ℕ) :
    graphFirstExponent t b = paperGraphFiber n 22 t b := rfl

theorem graph_fiber_label (t b : ℕ) :
    (graphFirstExponent t b + n - (22 * b) % n) % n = t % n := by
  simp only [graphFirstExponent]
  norm_num [n]
  omega

theorem phase_residue_on_every_fiber (t b : ℕ) :
    (17 * graphFirstExponent t b + 101728 * b) % q =
      (17 * t) % q := by
  simp only [graphFirstExponent]
  norm_num [n, q]
  omega

/- The numerator in Eq. (7.28) after the fiber substitution. It is a
   computable finite polynomial over every commutative semiring. -/
def fiberNumerator {R : Type*} [CommSemiring R] (root : R) (t : ℕ) : R :=
  (∑ b ∈ Finset.range n,
      root ^ ((17 * graphFirstExponent t b + 101728 * b) % q))

theorem source_fourier_equals_fiber {R : Type*} [CommSemiring R]
    (root : R) (t : ℕ) (ht : t < n) :
    paperFourierNumerator n q 22 17 101728 t root =
      fiberNumerator root t := by
  rw [source_fourier_fiber_reindex 17 101728 t root ht]
  rfl

theorem fiber_numerator_exact {R : Type*} [CommSemiring R]
    (root : R) (t : ℕ) :
    fiberNumerator root t = (n : R) * root ^ ((17 * t) % q) := by
  simp [fiberNumerator, phase_residue_on_every_fiber]

theorem fiber_amplitude_exact (root : ℂ) (t : ℕ) :
    fiberNumerator root t / ((n : ℂ) * (q : ℂ)) =
      root ^ ((17 * t) % q) / (q : ℂ) := by
  rw [fiber_numerator_exact]
  have hn : (n : ℂ) ≠ 0 := by norm_num [n]
  have hq : (q : ℂ) ≠ 0 := by norm_num [q]
  field_simp

theorem fiber_born_probability (root : ℂ)
    (hunit : Complex.normSq root = 1) (t : ℕ) :
    Complex.normSq
      (fiberNumerator root t / ((n : ℂ) * (q : ℂ))) =
      1 / (q : ℝ) ^ 2 := by
  have hpow (e : ℕ) : Complex.normSq (root ^ e) = 1 := by
    induction e with
    | zero => simp
    | succ e ih => simp [pow_succ, Complex.normSq_mul, hunit, ih]
  rw [fiber_amplitude_exact, Complex.normSq_div, hpow]
  simp [Complex.normSq_natCast, pow_two]

theorem good_pair_probability (root : ℂ)
    (hunit : Complex.normSq root = 1) :
    (∑ t ∈ Finset.range n,
      Complex.normSq
        (fiberNumerator root t / ((n : ℂ) * (q : ℂ)))) =
      (n : ℝ) / (q : ℝ) ^ 2 := by
  calc
    (∑ t ∈ Finset.range n,
        Complex.normSq
          (fiberNumerator root t / ((n : ℂ) * (q : ℂ)))) =
        ∑ _t ∈ Finset.range n, (1 / (q : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          exact fiber_born_probability root hunit t
    _ = (n : ℝ) / (q : ℝ) ^ 2 := by simp [div_eq_mul_inv]

theorem good_pair_probability_positive (root : ℂ)
    (hunit : Complex.normSq root = 1) :
    0 < ∑ t ∈ Finset.range n,
      Complex.normSq
        (fiberNumerator root t / ((n : ℂ) * (q : ℂ))) := by
  rw [good_pair_probability root hunit]
  norm_num [n, q]

/- The same ideal Fourier calculation holds for all 6006 good indices.
   The second frequency is reduced into [0,q); its quotient supplies the
   phase-grid integer in Eq. (7.34). -/
def goodSecondFrequency (j : ℕ) : ℕ := (101728 * j) % q

theorem every_index_is_complete_good_pair (j : ℕ) (hj : j < h) :
    GoodPair 22 (17 * j) (goodSecondFrequency j) (16 * j) 0
      ((j : ℤ) - (((101728 * j) / q : ℕ) : ℤ)) := by
  have hpartner :
      goodSecondFrequency j + q * ((101728 * j) / q) =
        101728 * j := by
    exact Nat.mod_add_div _ _
  have hpartnerZ :
      (goodSecondFrequency j : ℤ) +
        (q : ℤ) * ((((101728 * j) / q : ℕ) : ℤ)) =
      101728 * (j : ℤ) := by
    exact_mod_cast hpartner
  unfold GoodPair
  refine ⟨each_index_is_good j hj, ?_, ?_⟩
  · exact Nat.mod_lt _ (by norm_num [q])
  · have hzero :
        (22 : ℤ) * (17 * (j : ℤ)) + (goodSecondFrequency j : ℤ) -
          ((j : ℤ) - (((101728 * j) / q : ℕ) : ℤ)) * (q : ℤ) = 0 := by
      calc
        (22 : ℤ) * (17 * (j : ℤ)) + (goodSecondFrequency j : ℤ) -
            ((j : ℤ) - (((101728 * j) / q : ℕ) : ℤ)) * (q : ℤ) =
          (goodSecondFrequency j : ℤ) +
            (q : ℤ) * (((101728 * j) / q : ℕ) : ℤ) -
            101728 * (j : ℤ) := by norm_num [q]; ring
        _ = 0 := sub_eq_zero.mpr hpartnerZ
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    rw [hzero]
    norm_num [n]

theorem every_complete_good_pair_exact {c v cp : ℕ} {z J : ℤ}
    (hg : GoodPair 22 c v cp z J) :
    ∃ j : ℕ, j < h ∧ c = 17 * j ∧ cp = 16 * j ∧
      v = goodSecondFrequency j ∧ z = 0 := by
  obtain ⟨j, hj, hc, hcp, hz⟩ :=
    every_good_coefficient_shape hg.1
  refine ⟨j, hj, hc, hcp, ?_, hz⟩
  obtain ⟨_, hv, hphase⟩ := hg
  rw [hc, hz] at hphase
  simp only [Nat.cast_ofNat, mul_zero, sub_zero] at hphase
  have habsBound :
      |(22 : ℤ) * (17 * (j : ℤ)) +
          (v : ℤ) - J * (q : ℤ)| ≤ 0 := by
    norm_num [n, q] at hphase ⊢
    have habsZero :
        |22 * (17 * (j : ℤ)) + (v : ℤ) - J * 102102| = 0 := by
      have hnonneg :=
        abs_nonneg (22 * (17 * (j : ℤ)) + (v : ℤ) - J * 102102)
      omega
    exact abs_eq_zero.mp habsZero
  have habsParts := abs_le.mp habsBound
  have hvEq :
      374 * (j : ℤ) + (v : ℤ) = (q : ℤ) * J := by
    norm_num [q] at habsParts ⊢
    omega
  have hpartner :
      goodSecondFrequency j + q * ((101728 * j) / q) =
        101728 * j := by
    simpa [goodSecondFrequency] using
      (Nat.mod_add_div (101728 * j) q)
  have hpartnerZ :
      (goodSecondFrequency j : ℤ) +
          (q : ℤ) * (((101728 * j) / q : ℕ) : ℤ) =
        101728 * (j : ℤ) := by
    exact_mod_cast hpartner
  have hmodLt : goodSecondFrequency j < q := by
    unfold goodSecondFrequency
    exact Nat.mod_lt _ (by norm_num [q])
  norm_num [q] at hvEq hpartnerZ hv hmodLt ⊢
  omega

theorem every_complete_good_pair_has_unique_index
    {c v cp : ℕ} {z J : ℤ}
    (hg : GoodPair 22 c v cp z J) :
    ∃! j : ℕ, j < h ∧ c = 17 * j ∧ cp = 16 * j ∧
      v = goodSecondFrequency j ∧ z = 0 := by
  obtain ⟨j, hj, hc, hcp, hv, hz⟩ :=
    every_complete_good_pair_exact hg
  refine ⟨j, ⟨hj, hc, hcp, hv, hz⟩, ?_⟩
  intro y hy
  have hcy : c = 17 * y := hy.2.1
  omega

theorem complete_good_pair_iff_indexed (c v cp : ℕ) :
    (∃ z J : ℤ, GoodPair 22 c v cp z J) ↔
      ∃ j : ℕ, j < h ∧ c = 17 * j ∧ cp = 16 * j ∧
        v = goodSecondFrequency j := by
  constructor
  · rintro ⟨z, J, hg⟩
    obtain ⟨j, hj, hc, hcp, hv, _⟩ := every_complete_good_pair_exact hg
    exact ⟨j, hj, hc, hcp, hv⟩
  · rintro ⟨j, hj, rfl, rfl, rfl⟩
    exact ⟨0, (j : ℤ) - (((101728 * j) / q : ℕ) : ℤ),
      every_index_is_complete_good_pair j hj⟩

theorem phase_residue_all_good_indices (j t b : ℕ) :
    (17 * j * graphFirstExponent t b +
        goodSecondFrequency j * b) % q =
      (17 * j * t) % q := by
  let a : ℕ := graphFirstExponent t b
  let L : ℕ := (t + 22 * b) / n
  let v : ℕ := goodSecondFrequency j
  let m : ℕ := (101728 * j) / q
  have hcarry : a + n * L = t + 22 * b := by
    dsimp [a, L, graphFirstExponent]
    exact Nat.mod_add_div _ _
  have hpartner : v + q * m = 101728 * j := by
    dsimp [v, m, goodSecondFrequency]
    exact Nat.mod_add_div _ _
  have hphase :
      17 * j * a + v * b + q * (16 * j * L + m * b) =
        17 * j * t + q * j * b := by
    calc
      17 * j * a + v * b + q * (16 * j * L + m * b) =
          17 * j * (a + n * L) + (v + q * m) * b := by
            dsimp [n, q]
            ring
      _ = 17 * j * (t + 22 * b) + (101728 * j) * b := by
            rw [hcarry, hpartner]
      _ = 17 * j * t + q * j * b := by
            dsimp [q]
            ring
  have hmod :
      (17 * j * a + v * b) % q = (17 * j * t) % q := by
    calc
      (17 * j * a + v * b) % q =
          (17 * j * a + v * b + q * (16 * j * L + m * b)) % q := by
            simp [Nat.add_mod, Nat.mul_mod]
      _ = (17 * j * t + q * j * b) % q :=
        congrArg (fun x : ℕ => x % q) hphase
      _ = (17 * j * t) % q := by
        simp [Nat.add_mod, Nat.mul_mod, mul_assoc]
  simpa [a, v] using hmod

def fiberNumeratorAllGood {R : Type*} [CommSemiring R]
    (root : R) (j t : ℕ) : R :=
  ∑ b ∈ Finset.range n,
    root ^ ((17 * j * graphFirstExponent t b +
      goodSecondFrequency j * b) % q)

theorem source_fourier_equals_all_good {R : Type*} [CommSemiring R]
    (root : R) (j t : ℕ) (ht : t < n) :
    paperFourierNumerator n q 22 (17 * j) (goodSecondFrequency j) t root =
      fiberNumeratorAllGood root j t := by
  rw [source_fourier_fiber_reindex (17 * j) (goodSecondFrequency j) t root ht]
  rfl

theorem source_raw_fourier_equals_all_good {R : Type*} [CommSemiring R]
    (root : R) (hroot : root ^ q = 1) (j t : ℕ) (ht : t < n) :
    paperFourierRawNumerator n q 22 (17 * j) (goodSecondFrequency j) t root =
      fiberNumeratorAllGood root j t := by
  rw [raw_fourier_equals_reduced n q 22 (17 * j)
    (goodSecondFrequency j) t root hroot]
  exact source_fourier_equals_all_good root j t ht

theorem fiber_numerator_all_good {R : Type*} [CommSemiring R]
    (root : R) (j t : ℕ) :
    fiberNumeratorAllGood root j t =
      (n : R) * root ^ ((17 * j * t) % q) := by
  simp [fiberNumeratorAllGood, phase_residue_all_good_indices]

theorem fiber_amplitude_all_good (root : ℂ) (j t : ℕ) :
    fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ)) =
      root ^ ((17 * j * t) % q) / (q : ℂ) := by
  rw [fiber_numerator_all_good]
  have hn : (n : ℂ) ≠ 0 := by norm_num [n]
  have hq : (q : ℂ) ≠ 0 := by norm_num [q]
  field_simp

theorem fiber_born_all_good (root : ℂ)
    (hunit : Complex.normSq root = 1) (j t : ℕ) :
    Complex.normSq
      (fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ))) =
      1 / (q : ℝ) ^ 2 := by
  have hpow (e : ℕ) : Complex.normSq (root ^ e) = 1 := by
    induction e with
    | zero => simp
    | succ e ih => simp [pow_succ, Complex.normSq_mul, hunit, ih]
  rw [fiber_amplitude_all_good, Complex.normSq_div, hpow]
  simp [Complex.normSq_natCast, pow_two]

theorem pair_probability_all_good (root : ℂ)
    (hunit : Complex.normSq root = 1) (j : ℕ) :
    (∑ t ∈ Finset.range n,
      Complex.normSq
        (fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ)))) =
      (n : ℝ) / (q : ℝ) ^ 2 := by
  calc
    (∑ t ∈ Finset.range n,
        Complex.normSq
          (fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ)))) =
        ∑ _t ∈ Finset.range n, (1 / (q : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t _
          exact fiber_born_all_good root hunit j t
    _ = (n : ℝ) / (q : ℝ) ^ 2 := by simp [div_eq_mul_inv]

theorem source_raw_pair_probability_all_good (root : ℂ)
    (hroot : root ^ q = 1) (hunit : Complex.normSq root = 1)
    (j : ℕ) :
    (∑ t ∈ Finset.range n,
      Complex.normSq
        (paperFourierRawNumerator n q 22 (17 * j)
          (goodSecondFrequency j) t root /
          ((n : ℂ) * (q : ℂ)))) =
      (n : ℝ) / (q : ℝ) ^ 2 := by
  calc
    (∑ t ∈ Finset.range n,
      Complex.normSq
        (paperFourierRawNumerator n q 22 (17 * j)
          (goodSecondFrequency j) t root /
          ((n : ℂ) * (q : ℂ)))) =
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (fiberNumeratorAllGood root j t /
            ((n : ℂ) * (q : ℂ))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [source_raw_fourier_equals_all_good root hroot j t
          (Finset.mem_range.mp ht)]
    _ = (n : ℝ) / (q : ℝ) ^ 2 :=
      pair_probability_all_good root hunit j

theorem total_good_probability (root : ℂ)
    (hunit : Complex.normSq root = 1) :
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ)))) =
      (16 : ℝ) / 289 := by
  calc
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (fiberNumeratorAllGood root j t / ((n : ℂ) * (q : ℂ)))) =
      ∑ _j ∈ Finset.range h, (n : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact pair_probability_all_good root hunit j
    _ = (16 : ℝ) / 289 := by norm_num [n, q, h]

theorem source_raw_total_good_probability (root : ℂ)
    (hroot : root ^ q = 1) (hunit : Complex.normSq root = 1) :
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) =
      (16 : ℝ) / 289 := by
  calc
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) =
      ∑ _j ∈ Finset.range h, (n : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact source_raw_pair_probability_all_good root hroot hunit j
    _ = (16 : ℝ) / 289 := by norm_num [n, q, h]

def evenGoodIndices : Finset ℕ :=
  (Finset.range h).filter (fun j => 2 ∣ j)

theorem even_good_indices_exact :
    evenGoodIndices =
      (Finset.range 3003).image (fun r => 2 * r) := by
  ext j
  simp only [evenGoodIndices, Finset.mem_filter,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨hj, ⟨r, hr⟩⟩
    refine ⟨r, ?_, ?_⟩ <;> dsimp [h] at hj ⊢ <;> omega
  · rintro ⟨r, hr, rfl⟩
    constructor
    · dsimp [h]
      omega
    · exact ⟨r, by omega⟩

theorem even_good_indices_count : evenGoodIndices.card = 3003 := by
  rw [even_good_indices_exact]
  have hinj : Function.Injective (fun r : ℕ => 2 * r) := by
    intro a b hab
    dsimp at hab
    omega
  simpa using
    (Finset.card_image_of_injective (Finset.range 3003) hinj)

theorem source_raw_divisible_good_probability (root : ℂ)
    (hroot : root ^ q = 1) (hunit : Complex.normSq root = 1) :
    (∑ j ∈ evenGoodIndices,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) =
      (8 : ℝ) / 289 := by
  calc
    (∑ j ∈ evenGoodIndices,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) =
      ∑ _j ∈ evenGoodIndices, (n : ℝ) / (q : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact source_raw_pair_probability_all_good root hroot hunit j
    _ = (8 : ℝ) / 289 := by
      simp only [Finset.sum_const, nsmul_eq_mul, even_good_indices_count]
      norm_num [n, q]

theorem physical_conditional_bound_false (root : ℂ)
    (hroot : root ^ q = 1) (hunit : Complex.normSq root = 1) :
    (∑ j ∈ evenGoodIndices,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) /
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) = (1 : ℝ) / 2 ∧
    (10 : ℝ) / 32 < (1 : ℝ) / 2 := by
  rw [source_raw_divisible_good_probability root hroot hunit,
    source_raw_total_good_probability root hroot hunit]
  norm_num

/- The source QFT's explicit complex phase is certified without an
   executable real-valued definition. -/
theorem explicit_qft_root_pow :
    (Complex.exp
      (((2 * Real.pi / (102102 : ℝ) : ℝ) : ℂ) * Complex.I)) ^ q = 1 := by
  change (Complex.exp
    (((2 * Real.pi / (102102 : ℝ) : ℝ) : ℂ) * Complex.I)) ^ 102102 = 1
  rw [← Complex.exp_nat_mul]
  have harg :
      ((102102 : ℕ) : ℂ) *
          (((2 * Real.pi / (102102 : ℝ) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg]
  exact Complex.exp_two_pi_mul_I

theorem explicit_qft_root_normSq_one :
    Complex.normSq
      (Complex.exp
        (((2 * Real.pi / (102102 : ℝ) : ℝ) : ℂ) * Complex.I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem explicit_qft_root_primitive :
    IsPrimitiveRoot
      (Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I / (102102 : ℂ))) q := by
  change IsPrimitiveRoot
    (Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I / (102102 : ℂ))) 102102
  exact Complex.isPrimitiveRoot_exp 102102 (by norm_num)

theorem actual_qft_conditional_bound_false :
    let root : ℂ := Complex.exp
      (((2 * Real.pi / (102102 : ℝ) : ℝ) : ℂ) * Complex.I)
    (∑ j ∈ evenGoodIndices,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) /
    (∑ j ∈ Finset.range h,
      ∑ t ∈ Finset.range n,
        Complex.normSq
          (paperFourierRawNumerator n q 22 (17 * j)
            (goodSecondFrequency j) t root /
            ((n : ℂ) * (q : ℂ)))) = (1 : ℝ) / 2 ∧
    (10 : ℝ) / 32 < (1 : ℝ) / 2 := by
  exact physical_conditional_bound_false _
    explicit_qft_root_pow explicit_qft_root_normSq_one

#print PaperUnitExistenceClaim
#print axioms p_is_prime
#print axioms paper_modulus_certificate
#print axioms prime_prefix_complete
#print axioms no_larger_removable_factor
#print axioms every_good_coefficient_shape
#print axioms good_first_iff_exact_lattice
#print axioms divisible_good_coefficient_count
#print axioms printed_ten_over_thirty_two_bound_false
#print axioms paper_unit_existence_claim_false
#print axioms paper_complete_pair_unit_claim_false
#print axioms explicit_complete_good_pair
#print axioms phase_residue_on_every_fiber
#print axioms paper_rounding_and_congruence
#print axioms source_graph_fiber_iff
#print axioms source_fourier_fiber_reindex
#print axioms source_raw_fourier_equals_all_good
#print axioms source_raw_pair_probability_all_good
#print axioms total_good_probability
#print axioms source_raw_total_good_probability
#print axioms physical_conditional_bound_false
#print axioms explicit_qft_root_primitive
#print axioms actual_qft_conditional_bound_false
#print axioms complete_good_pair_iff_indexed
#print axioms every_index_is_complete_good_pair
#print axioms every_complete_good_pair_exact
#print axioms fiber_numerator_exact
#print axioms good_pair_probability

end Shor1994Invalidation
