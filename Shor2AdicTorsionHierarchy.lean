import Mathlib

namespace Shor2AdicTorsionHierarchy

open scoped BigOperators

/-!
SECTION 1: BINARY CONTROL MULTIPLIERS AND RESIDUE FIBER SHIFTS
For n = 2^r m, keys k + s m have identical multipliers at stages j >= r.
These equalities alone do not assert equality of complete quantum states.
Within one fixed residue class b = d beta + rem, a key shift translates t.
The finite reindexing lemma concerns a common fiber shift. Coherent sums
across distinct residue classes also contain cross terms.
-/

theorem binary_control_stage_invariance
    (r m j k s : ℕ) (hj : r ≤ j) :
    (2 ^ j * (k + s * m)) % (2 ^ r * m) =
      (2 ^ j * k) % (2 ^ r * m) := by
  have hsplit : j = (j - r) + r := (Nat.sub_add_cancel hj).symm
  have hmul :
      2 ^ j * (k + s * m) =
        2 ^ j * k + (s * 2 ^ (j - r)) * (2 ^ r * m) := by
    calc
      2 ^ j * (k + s * m) = 2 ^ j * k + 2 ^ j * (s * m) := by ring
      _ = 2 ^ j * k + 2 ^ ((j - r) + r) * (s * m) := by rw [← hsplit]
      _ = 2 ^ j * k + (2 ^ (j - r) * 2 ^ r) * (s * m) := by rw [pow_add]
      _ = 2 ^ j * k + (s * 2 ^ (j - r)) * (2 ^ r * m) := by ring
  rw [hmul, Nat.add_mul_mod_self_right]

/-- Arithmetic certificate at modulus 116: keys 22 and 80 have identical
    multipliers on stages 1 through 6 and different multipliers on stage 0. -/
theorem elliptic_116_six_of_seven_controls_identical :
    (∀ j ∈ Finset.Icc 1 6,
      (2 ^ j * 80) % 116 = (2 ^ j * 22) % 116) ∧
    (2 ^ 0 * 80) % 116 ≠ (2 ^ 0 * 22) % 116 := by
  decide

/-- At modulus 116, the four keys {22, 51, 80, 109} have identical
    multipliers on stages 2 through 6. No elliptic curve is defined here. -/
theorem elliptic_116_mod4_upper_controls_identical :
    ∀ j ∈ Finset.Icc 2 6,
      (2 ^ j * 51) % 116 = (2 ^ j * 22) % 116 ∧
      (2 ^ j * 80) % 116 = (2 ^ j * 22) % 116 ∧
      (2 ^ j * 109) % 116 = (2 ^ j * 22) % 116 := by
  decide

/-- In Shor's multiplicative group F_101* with n = 100 and q = 128, keys 22 and 72
    have identical controlled multiples on stages j = 1..6 and differ only at j = 0. -/
theorem shor_100_six_of_seven_controls_identical :
    (∀ j ∈ Finset.Icc 1 6,
      (2 ^ j * 72) % 100 = (2 ^ j * 22) % 100) ∧
    (2 ^ 0 * 72) % 100 ≠ (2 ^ 0 * 22) % 100 := by
  decide

/-- In F_101* with p = 101, g = 2, n = 100, g^72 = 24 ≡ -77 = -g^22 (mod 101). -/
theorem shor_101_multiplicative_sign_flip :
    (2 ^ 22) % 101 = 77 ∧
    (2 ^ 72) % 101 = 24 ∧
    (77 + 24) % 101 = 0 := by
  decide

/-- When b and b' share the same residue modulo d (where n = d * m),
    k_s * (b - b') ≡ k * (b - b') (mod n) for all s. -/
theorem coherence_block_phase_difference_invariance
    (d m k s : ℤ) (q1 q2 rem : ℤ) :
    ((k + s * m) * ((d * q1 + rem) - (d * q2 + rem))) % (d * m) =
      (k * ((d * q1 + rem) - (d * q2 + rem))) % (d * m) := by
  have hsplit :
      (k + s * m) * ((d * q1 + rem) - (d * q2 + rem)) =
        k * ((d * q1 + rem) - (d * q2 + rem)) +
          (d * m) * (s * (q1 - q2)) := by
    ring
  rw [hsplit, Int.add_mul_emod_self_left]

/-- On the residue class b = d * beta + rem, shifting k by s * m translates
    the fiber index t by s * m * rem modulo n = d * m. -/
theorem residue_class_fiber_shift
    (d m t k s beta rem : ℕ) :
    (t + (k + s * m) * (d * beta + rem)) % (d * m) =
      ((t + s * m * rem) + k * (d * beta + rem)) % (d * m) := by
  have hsplit :
      t + (k + s * m) * (d * beta + rem) =
        ((t + s * m * rem) + k * (d * beta + rem)) +
          (s * beta) * (d * m) := by
    ring
  rw [hsplit, Nat.add_mul_mod_self_right]

def residueClassFiberNumerator {R : Type*} [CommSemiring R]
    (d m q k u v rem t : ℕ) (root : R) : R :=
  ∑ beta ∈ Finset.range m,
    root ^ ((u * ((t + k * (d * beta + rem)) % (d * m)) +
      v * (d * beta + rem)) % q)

theorem residue_class_numerator_shifted_fiber {R : Type*} [CommSemiring R]
    (d m q k s u v rem t : ℕ) (root : R) :
    residueClassFiberNumerator d m q (k + s * m) u v rem t root =
      residueClassFiberNumerator d m q k u v rem (t + s * m * rem) root := by
  unfold residueClassFiberNumerator
  apply Finset.sum_congr rfl
  intro beta _
  rw [residue_class_fiber_shift]

/-- Reindexing a sum over all fibers by a common additive shift. -/
theorem zmod_fiber_sum_invariant_on_residue_class
    {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (F : (ZMod n → ZMod n) → M) (k : ZMod n) (shift : ZMod n) :
    (∑ t : ZMod n, F (fun beta => t + (k * beta + shift))) =
      ∑ t : ZMod n, F (fun beta => t + k * beta) := by
  have hrew :
      (∑ t : ZMod n, F (fun beta => t + (k * beta + shift))) =
        ∑ t : ZMod n, F (fun beta => (t + shift) + k * beta) := by
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    ext beta
    ring
  rw [hrew]
  exact Fintype.sum_equiv (Equiv.addRight shift) _ _ (fun _ => rfl)

/-!
===========================================================================
SECTION 2: DUAL LATTICE COLLAPSE (1994 q/20 & 1997 q/12 WINDOWS + COSETS)
===========================================================================
In the decoding congruence `k * c' + e = n * J`, whenever `d ∣ c'` and
`n = d * m`, every key `k_s = k + s * m` in the d-torsion coset satisfies
the exact same rounding congruence. When `Q = q / gcd(n, q) < 12` (1997)
or `Q < 20` (1994), `z = 0` and `c' = N * j`, forcing every good outcome
to collapse onto multiples of `N = n / gcd(n, q)`.
-/

theorem rounded_congruence_satisfied_by_entire_coset
    {d m c0 k e J : ℤ}
    (hcong : k * (d * c0) + e = (d * m) * J) (s : ℤ) :
    (k + s * m) * (d * c0) + e = (d * m) * (J + s * c0) := by
  have hident :
      (k + s * m) * (d * c0) + e =
        (k * (d * c0) + e) + (d * m) * (s * c0) := by
    ring
  linarith

theorem modular_congruence_coset_invariance
    (d m c0 k s e : ℕ) :
    ((d * c0) * (k + s * m) + e) % (d * m) =
      ((d * c0) * k + e) % (d * m) := by
  have hsplit :
      (d * c0) * (k + s * m) + e =
        ((d * c0) * k + e) + (c0 * s) * (d * m) := by
    ring
  rw [hsplit, Nat.add_mul_mod_self_right]

/-- Shor's 1997 Expanded Paper Eq. (6.11) good-frequency window `|z| ≤ q/12`. -/
abbrev GoodFirst1997 (n q c cp : ℕ) (z : ℤ) : Prop :=
  c < q ∧ cp < n ∧
  (n : ℤ) * (c : ℤ) = (q : ℤ) * (cp : ℤ) + z ∧
  -(q : ℤ) < 2 * z ∧ 2 * z ≤ (q : ℤ) ∧
  12 * |z| ≤ (q : ℤ)

theorem good_residue_zero_1997
    {h N Q c cp : ℕ} {z : ℤ}
    (hh : 0 < h) (hQlt : Q < 12)
    (hg : GoodFirst1997 (h * N) (h * Q) c cp z) : z = 0 := by
  obtain ⟨_, _, heq, _, _, hwindow⟩ := hg
  have hhZ : 0 < (h : ℤ) := by exact_mod_cast hh
  have hQZ : (Q : ℤ) < 12 := by exact_mod_cast hQlt
  let w : ℤ := (N : ℤ) * (c : ℤ) - (Q : ℤ) * (cp : ℤ)
  have hzfactor : z = (h : ℤ) * w := by
    dsimp [w]
    push_cast at heq
    nlinarith [heq]
  have habsfactor : |z| = (h : ℤ) * |w| := by
    rw [hzfactor, abs_mul, abs_of_pos hhZ]
  rw [habsfactor] at hwindow
  push_cast at hwindow
  have hscaled : (h : ℤ) * (12 * |w|) ≤ (h : ℤ) * (Q : ℤ) := by
    calc
      (h : ℤ) * (12 * |w|) = 12 * ((h : ℤ) * |w|) := by ring
      _ ≤ (h : ℤ) * (Q : ℤ) := hwindow
  have hsmall : 12 * |w| ≤ (Q : ℤ) :=
    le_of_mul_le_mul_left hscaled hhZ
  have habslt : |w| < 1 := by omega
  have habszero : |w| = 0 := by
    have hnonneg := abs_nonneg w
    omega
  have hwzero : w = 0 := abs_eq_zero.mp habszero
  rw [hzfactor, hwzero, mul_zero]

theorem every_good_coefficient_shape_1997
    {h N Q c cp : ℕ} {z : ℤ}
    (hh : 0 < h) (hQ : 0 < Q) (hQlt : Q < 12)
    (hcop : Nat.Coprime N Q)
    (hg : GoodFirst1997 (h * N) (h * Q) c cp z) :
    ∃ j : ℕ, j < h ∧ c = Q * j ∧ cp = N * j ∧ z = 0 := by
  have hz : z = 0 := good_residue_zero_1997 hh hQlt hg
  obtain ⟨hc, _, heq, _, _, _⟩ := hg
  have hhZ : (h : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  have hscaled :
      (h : ℤ) * ((N : ℤ) * (c : ℤ)) =
        (h : ℤ) * ((Q : ℤ) * (cp : ℤ)) := by
    push_cast at heq
    rw [hz, add_zero] at heq
    simpa only [mul_assoc] using heq
  have hrelZ : (N : ℤ) * (c : ℤ) = (Q : ℤ) * (cp : ℤ) :=
    mul_left_cancel₀ hhZ hscaled
  have hrel : N * c = Q * cp := by exact_mod_cast hrelZ
  have hdiv : Q ∣ c := (hcop.symm.dvd_mul_left).mp ⟨cp, hrel⟩
  obtain ⟨j, hcj⟩ := hdiv
  have hcpj : cp = N * j := by
    apply Nat.eq_of_mul_eq_mul_left hQ
    calc
      Q * cp = N * c := hrel.symm
      _ = Q * (N * j) := by rw [hcj]; ring
  have hj : j < h := by
    have hbound : Q * j < Q * h := by
      simpa only [hcj, mul_comm h Q] using hc
    exact Nat.lt_of_mul_lt_mul_left hbound
  exact ⟨j, hj, hcj, hcpj, hz⟩

/-- First-frequency window and congruence candidates for table row 1.
    The second-frequency phase inequality is certified in Shor2AdicQFTBridge. -/
theorem shor_100_good_table_row_1 :
    GoodFirst1997 100 128 9 7 4 ∧
    Nat.gcd 7 100 = 1 ∧
    (Finset.range 100).filter (fun k => (7 * k + 46) % 100 = 0) = {22} := by
  decide

/-- The q/12 first-frequency test and congruence candidates for row 2.
    This row does not satisfy the narrower q/20 first-frequency test. -/
theorem shor_100_good_table_row_2 :
    GoodFirst1997 100 128 18 14 8 ∧
    Nat.gcd 14 100 = 2 ∧
    (Finset.range 100).filter (fun k => (14 * k + 92) % 100 = 0) = {22, 72} := by
  decide

/-- First-frequency window and congruence candidates for row 3. -/
theorem shor_100_good_table_row_3 :
    GoodFirst1997 100 128 41 32 4 ∧
    Nat.gcd 32 100 = 4 ∧
    (Finset.range 100).filter (fun k => (32 * k + 96) % 100 = 0) =
      {22, 47, 72, 97} := by
  decide

/-!
===========================================================================
SECTION 3: UNIVERSAL PADDED QFT TORSION ZERO-COLUMN LAW (v = 32, 96)
===========================================================================
When `gcd(k, n) = d > 1` (`n = d * n0`, `k = d * k0`), the integer remainder
`a(t, b) = (t + k * b) % n` is strictly periodic in `b` with period `n0`.
Consequently, for ANY padded QFT dimension `q`, the raw character sum
factors out the Universal Torsion Filter `Φ_d(v) = ∑_{j < d} root^(v * j * n0)`.
When `d = 2` (`n = 2 * n0`, `k = 2 * k0`), `Φ_2(v) = 1 + root^(v * n0)`,
which vanishes identically across all `u` and all fibers `t` whenever
`root^(v * n0) = -1` (producing the exact zero columns at `v = 32, 96`).
-/

def paddedGraphFiber (n k t b : ℕ) : ℕ := (t + k * b) % n

theorem padded_graph_fiber_period_step
    (d n0 k0 t j r : ℕ) :
    paddedGraphFiber (d * n0) (d * k0) t (j * n0 + r) =
      paddedGraphFiber (d * n0) (d * k0) t r := by
  unfold paddedGraphFiber
  have hsplit :
      t + (d * k0) * (j * n0 + r) =
        (t + (d * k0) * r) + (k0 * j) * (d * n0) := by
    ring
  rw [hsplit, Nat.add_mul_mod_self_right]

theorem padded_graph_fiber_half_period
    (n0 k0 t r : ℕ) :
    paddedGraphFiber (2 * n0) (2 * k0) t (n0 + r) =
      paddedGraphFiber (2 * n0) (2 * k0) t r := by
  have h := padded_graph_fiber_period_step 2 n0 k0 t 1 r
  simpa only [one_mul] using h

def rawPaddedFiberSum {R : Type*} [CommRing R]
    (n k u v t : ℕ) (root : R) : R :=
  ∑ b ∈ Finset.range n,
    root ^ (u * paddedGraphFiber n k t b + v * b)

/-- Universal d-fold torsion factorization of the unreduced padded QFT sum. -/
theorem raw_padded_general_torsion_factorization {R : Type*} [CommRing R]
    (d n0 k0 u v t : ℕ) (root : R) (g : ℕ) :
    (∑ b ∈ Finset.range (g * n0),
      root ^ (u * paddedGraphFiber (d * n0) (d * k0) t b + v * b)) =
    (∑ j ∈ Finset.range g, root ^ (v * (j * n0))) *
      (∑ r ∈ Finset.range n0,
        root ^ (u * paddedGraphFiber (d * n0) (d * k0) t r + v * r)) := by
  induction g with
  | zero =>
    simp
  | succ g ih =>
    have hrange : Finset.range ((g + 1) * n0) = Finset.range (g * n0 + n0) := by
      congr 1
      ring
    rw [hrange, Finset.sum_range_add, ih]
    have hblock :
        (∑ r ∈ Finset.range n0,
          root ^ (u * paddedGraphFiber (d * n0) (d * k0) t (g * n0 + r) +
            v * (g * n0 + r))) =
        root ^ (v * (g * n0)) *
          (∑ r ∈ Finset.range n0,
            root ^ (u * paddedGraphFiber (d * n0) (d * k0) t r + v * r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [padded_graph_fiber_period_step]
      have hexp :
          u * paddedGraphFiber (d * n0) (d * k0) t r + v * (g * n0 + r) =
            v * (g * n0) +
              (u * paddedGraphFiber (d * n0) (d * k0) t r + v * r) := by
        ring
      rw [hexp, pow_add]
    rw [hblock, Finset.sum_range_succ]
    ring

/-- Order-2 torsion factorization: `1 + root^(v * n0)` factors out for all `(u, t)`. -/
theorem raw_padded_fiber_sum_factorization {R : Type*} [CommRing R]
    (n0 k0 u v t : ℕ) (root : R) :
    rawPaddedFiberSum (2 * n0) (2 * k0) u v t root =
      (1 + root ^ (v * n0)) *
        ∑ r ∈ Finset.range n0,
          root ^ (u * paddedGraphFiber (2 * n0) (2 * k0) t r + v * r) := by
  unfold rawPaddedFiberSum
  have hrange : Finset.range (2 * n0) = Finset.range (n0 + n0) := by
    rw [Nat.two_mul]
  rw [hrange, Finset.sum_range_add]
  have hsecond :
      (∑ r ∈ Finset.range n0,
        root ^ (u * paddedGraphFiber (2 * n0) (2 * k0) t (n0 + r) +
          v * (n0 + r))) =
      root ^ (v * n0) *
        ∑ r ∈ Finset.range n0,
          root ^ (u * paddedGraphFiber (2 * n0) (2 * k0) t r + v * r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [padded_graph_fiber_half_period]
    have hexp :
        u * paddedGraphFiber (2 * n0) (2 * k0) t r + v * (n0 + r) =
          v * n0 + (u * paddedGraphFiber (2 * n0) (2 * k0) t r + v * r) := by
      ring
    rw [hexp, pow_add]
  rw [hsecond]
  ring

/-- Universal Zero-Column Law: when `root^(v * n0) = -1`, the entire column `v`
    vanishes for every first frequency `u` and every fiber `t`. -/
theorem zero_column_of_half_period_neg_one {R : Type*} [CommRing R]
    (n0 k0 u v t : ℕ) (root : R)
    (hneg : root ^ (v * n0) = -1) :
    rawPaddedFiberSum (2 * n0) (2 * k0) u v t root = 0 := by
  rw [raw_padded_fiber_sum_factorization, hneg, add_neg_cancel, zero_mul]

/-- Residue certificates at q = 128. Shor2AdicQFTBridge combines these with
    the actual complex QFT root to prove the zero-column amplitudes. -/
theorem elliptic_116_and_shor_100_zero_column_frequencies :
    (32 * 58) % 128 = 64 ∧ (96 * 58) % 128 = 64 ∧
    (32 * 50) % 128 = 64 ∧ (96 * 50) % 128 = 64 := by
  decide

/-!
SECTION 4: PARITY IDENTITIES AND FINITE SUM REINDEXING
The two Hadamard square identities use different coefficient rings.
The Boolean sign character has period two in its first argument.
The parity twist shifts the unreduced second-frequency exponent.
The first-marginal statement is an abstract finite reindexing identity.
The second-marginal statement is an abstract collision-sum identity;
a physical Born-marginal claim additionally requires its Fourier expansion.
-/

def hadamardUnnorm (i j : Fin 2) : ℤ :=
  if i = 1 ∧ j = 1 then -1 else 1

def hadamardMod2 (_i _j : Fin 2) : ZMod 2 := 1

theorem hadamard_int_sq_eq_two_id :
    ∀ i k : Fin 2,
      (∑ j : Fin 2, hadamardUnnorm i j * hadamardUnnorm j k) =
        if i = k then 2 else 0 := by
  decide

theorem hadamard_mod2_sq_eq_zero :
    ∀ i k : Fin 2,
      (∑ j : Fin 2, hadamardMod2 i j * hadamardMod2 j k) = 0 := by
  decide

def booleanSignCharacter (u a : ℕ) : ℤ := (-1 : ℤ) ^ (u * a)

theorem boolean_sign_character_period_two (u a : ℕ) :
    booleanSignCharacter (u + 2) a = booleanSignCharacter u a := by
  unfold booleanSignCharacter
  have hexp : (u + 2) * a = u * a + 2 * a := by ring
  rw [hexp, pow_add, pow_mul]
  norm_num

/-- Applying the parity phase `(-1)^b` inside the fiber sum shifts `v` to `v + q0`. -/
theorem parity_twist_shifts_second_frequency {R : Type*} [CommRing R]
    (n k u v t q0 : ℕ) (root : R) (hhalf : root ^ q0 = -1) :
    (∑ b ∈ Finset.range n,
      (-1 : R) ^ b *
        root ^ (u * paddedGraphFiber n k t b + v * b)) =
    rawPaddedFiberSum n k u (v + q0) t root := by
  unfold rawPaddedFiberSum
  apply Finset.sum_congr rfl
  intro b _
  rw [← hhalf, ← pow_mul]
  have hexp :
      u * paddedGraphFiber n k t b + (v + q0) * b =
        q0 * b + (u * paddedGraphFiber n k t b + v * b) := by
    ring
  rw [hexp]
  simp only [pow_add]

/-- First-Marginal Invariance: shifting the second frequency `v ↦ v + delta`
    leaves the first-register marginal `P(u) = ∑_v P(u, v)` identically unchanged. -/
theorem first_marginal_invariant_of_frequency_shift
    {q : ℕ} [NeZero q]
    (P : ZMod q → ZMod q → ℝ) (delta : ZMod q) (u : ZMod q) :
    (∑ v : ZMod q, P u (v + delta)) = ∑ v : ZMod q, P u v := by
  exact Fintype.sum_equiv (Equiv.addRight delta) _ _ (fun _ => rfl)

/-- For an even quotient n/d and an odd quotient k/d, a modular collision
    forces an even difference. The hypotheses do not require d = gcd(k,n). -/
theorem even_reduced_order_collision_even_diff
    {d m0 s0 b b' : ℤ} (hd : d ≠ 0)
    (hcoll : (d * (2 * m0)) ∣ (d * (2 * s0 + 1)) * (b - b')) :
    (2 : ℤ) ∣ (b - b') := by
  have hmul :
      (d * (2 * s0 + 1)) * (b - b') =
        d * ((2 * s0 + 1) * (b - b')) := by
    ring
  rw [hmul] at hcoll
  have hcancel : (2 * m0) ∣ (2 * s0 + 1) * (b - b') :=
    (mul_dvd_mul_iff_left hd).mp hcoll
  have htwo_dvd_prod : (2 : ℤ) ∣ (2 * s0 + 1) * (b - b') :=
    ( dvd_mul_right 2 m0 ).trans hcancel
  obtain ⟨w, hw⟩ := htwo_dvd_prod
  refine ⟨w - s0 * (b - b'), ?_⟩
  linarith

/-- Whenever two natural exponents `b, b'` share the same parity,
    `(-1)^b * (-1)^b' = 1` in every commutative ring. -/
theorem parity_phase_product_one_of_same_parity {R : Type*} [CommRing R]
    (b b' : ℕ) (hpar : b % 2 = b' % 2) :
    (-1 : R) ^ b * (-1 : R) ^ b' = 1 := by
  rw [← pow_add]
  have heven : 2 ∣ (b + b') := by omega
  obtain ⟨m, hm⟩ := heven
  rw [hm, pow_mul]
  norm_num

/-- On a collision set with equal parities, the parity factors cancel termwise.
    The function phase is arbitrary; this theorem does not define a Born marginal. -/
theorem second_marginal_invariant_of_even_collisions
    {R : Type*} [CommRing R]
    (n : ℕ) (collides : ℕ → ℕ → ℕ → Prop)
    [∀ t b b', Decidable (collides t b b')]
    (hpar : ∀ t b b', collides t b b' → b % 2 = b' % 2)
    (phase : ℕ → ℕ → ℕ → R) :
    (∑ t ∈ Finset.range n,
      ∑ b ∈ Finset.range n,
        ∑ b' ∈ Finset.range n,
          if collides t b b' then
            ((-1 : R) ^ b * (-1 : R) ^ b') * phase t b b'
          else 0) =
    (∑ t ∈ Finset.range n,
      ∑ b ∈ Finset.range n,
        ∑ b' ∈ Finset.range n,
          if collides t b b' then
            phase t b b'
          else 0) := by
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro b' _
  by_cases hc : collides t b b'
  · simp only [hc, ite_true]
    rw [parity_phase_product_one_of_same_parity b b' (hpar t b b' hc), one_mul]
  · simp [hc]

/-- Modular collisions at moduli 116 and 100 preserve parity. -/
theorem elliptic_116_and_shor_100_collisions_preserve_parity :
    (∀ b ∈ Finset.range 116, ∀ b' ∈ Finset.range 116,
      (22 * b) % 116 = (22 * b') % 116 → b % 2 = b' % 2) ∧
    (∀ b ∈ Finset.range 100, ∀ b' ∈ Finset.range 100,
      (22 * b) % 100 = (22 * b') % 100 → b % 2 = b' % 2) := by
  constructor
  · intro b _ b' _ hcoll
    omega
  · intro b _ b' _ hcoll
    omega

#print axioms binary_control_stage_invariance
#print axioms elliptic_116_six_of_seven_controls_identical
#print axioms elliptic_116_mod4_upper_controls_identical
#print axioms shor_100_six_of_seven_controls_identical
#print axioms shor_101_multiplicative_sign_flip
#print axioms coherence_block_phase_difference_invariance
#print axioms residue_class_fiber_shift
#print axioms residue_class_numerator_shifted_fiber
#print axioms zmod_fiber_sum_invariant_on_residue_class
#print axioms rounded_congruence_satisfied_by_entire_coset
#print axioms modular_congruence_coset_invariance
#print axioms good_residue_zero_1997
#print axioms every_good_coefficient_shape_1997
#print axioms shor_100_good_table_row_1
#print axioms shor_100_good_table_row_2
#print axioms shor_100_good_table_row_3
#print axioms padded_graph_fiber_period_step
#print axioms padded_graph_fiber_half_period
#print axioms raw_padded_general_torsion_factorization
#print axioms raw_padded_fiber_sum_factorization
#print axioms zero_column_of_half_period_neg_one
#print axioms elliptic_116_and_shor_100_zero_column_frequencies
#print axioms hadamard_int_sq_eq_two_id
#print axioms hadamard_mod2_sq_eq_zero
#print axioms boolean_sign_character_period_two
#print axioms parity_twist_shifts_second_frequency
#print axioms first_marginal_invariant_of_frequency_shift
#print axioms even_reduced_order_collision_even_diff
#print axioms parity_phase_product_one_of_same_parity
#print axioms second_marginal_invariant_of_even_collisions
#print axioms elliptic_116_and_shor_100_collisions_preserve_parity

end Shor2AdicTorsionHierarchy
