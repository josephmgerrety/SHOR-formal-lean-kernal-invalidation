import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Init.Omega

namespace ShorWindowFamily

/- The original centered-residue and q/20 good-frequency conditions. -/
def GoodFirst (n q c cp : ℕ) (z : ℤ) : Prop :=
  c < q ∧ cp < n ∧
  (n : ℤ) * (c : ℤ) = (q : ℤ) * (cp : ℤ) + z ∧
  -(q : ℤ) < 2 * z ∧ 2 * z ≤ (q : ℤ) ∧
  20 * |z| ≤ (q : ℤ)

theorem good_residue_zero
    {h N Q c cp : ℕ} {z : ℤ}
    (hh : 0 < h) (hQlt : Q < 20)
    (hg : GoodFirst (h * N) (h * Q) c cp z) : z = 0 := by
  obtain ⟨_, _, heq, _, _, hwindow⟩ := hg
  have hhZ : 0 < (h : ℤ) := by exact_mod_cast hh
  have hQZ : (Q : ℤ) < 20 := by exact_mod_cast hQlt
  let w : ℤ := (N : ℤ) * (c : ℤ) - (Q : ℤ) * (cp : ℤ)
  have hzfactor : z = (h : ℤ) * w := by
    dsimp [w]
    push_cast at heq
    nlinarith [heq]
  have habsfactor : |z| = (h : ℤ) * |w| := by
    rw [hzfactor, abs_mul, abs_of_pos hhZ]
  rw [habsfactor] at hwindow
  push_cast at hwindow
  have hscaled : (h : ℤ) * (20 * |w|) ≤ (h : ℤ) * (Q : ℤ) := by
    calc
      (h : ℤ) * (20 * |w|) = 20 * ((h : ℤ) * |w|) := by ring
      _ ≤ (h : ℤ) * (Q : ℤ) := hwindow
  have hsmall : 20 * |w| ≤ (Q : ℤ) := le_of_mul_le_mul_left hscaled hhZ
  have habslt : |w| < 1 := by omega
  have habszero : |w| = 0 := by
    have hnonneg := abs_nonneg w
    omega
  have hwzero : w = 0 := abs_eq_zero.mp habszero
  rw [hzfactor, hwzero, mul_zero]

theorem every_good_coefficient_shape
    {h N Q c cp : ℕ} {z : ℤ}
    (hh : 0 < h) (hQ : 0 < Q) (hQlt : Q < 20)
    (hcop : Nat.Coprime N Q)
    (hg : GoodFirst (h * N) (h * Q) c cp z) :
    ∃ j : ℕ, j < h ∧ c = Q * j ∧ cp = N * j ∧ z = 0 := by
  have hz : z = 0 := good_residue_zero hh hQlt hg
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
  have hdiv : Q ∣ c :=
    (hcop.symm.dvd_mul_left).mp ⟨cp, hrel⟩
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

theorem each_index_is_good
    {h N Q j : ℕ}
    (hh : 0 < h) (hN : 0 < N) (hQ : 0 < Q) (hj : j < h) :
    GoodFirst (h * N) (h * Q) (Q * j) (N * j) 0 := by
  have hqpos : (0 : ℤ) < (h : ℤ) * (Q : ℤ) := by
    exact_mod_cast (Nat.mul_pos hh hQ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_comm h Q] using Nat.mul_lt_mul_of_pos_left hj hQ
  · simpa only [mul_comm h N] using Nat.mul_lt_mul_of_pos_left hj hN
  · push_cast
    ring
  · push_cast
    linarith
  · push_cast
    linarith
  · push_cast
    norm_num
    positivity

theorem good_first_iff_exact_lattice
    {h N Q c cp : ℕ} {z : ℤ}
    (hh : 0 < h) (hN : 0 < N) (hQ : 0 < Q) (hQlt : Q < 20)
    (hcop : Nat.Coprime N Q) :
    GoodFirst (h * N) (h * Q) c cp z ↔
      ∃ j : ℕ, j < h ∧ c = Q * j ∧ cp = N * j ∧ z = 0 := by
  constructor
  · exact every_good_coefficient_shape hh hQ hQlt hcop
  · rintro ⟨j, hj, rfl, rfl, rfl⟩
    exact each_index_is_good hh hN hQ hj

theorem no_good_unit_of_common_factor
    {h N Q c cp ell R : ℕ} {z : ℤ}
    (hh : 0 < h) (hQ : 0 < Q) (hQlt : Q < 20)
    (hcop : Nat.Coprime N Q)
    (hell : 1 < ell) (hellN : ell ∣ N) (hellR : ell ∣ R)
    (hg : GoodFirst (h * N) (h * Q) c cp z) :
    ¬ Nat.Coprime cp R := by
  intro hunit
  obtain ⟨j, _, _, hcp, _⟩ :=
    every_good_coefficient_shape hh hQ hQlt hcop hg
  have hNcp : N ∣ cp := ⟨j, hcp⟩
  have hellcp : ell ∣ cp := hellN.trans hNcp
  have hellgcd : ell ∣ Nat.gcd cp R := Nat.dvd_gcd hellcp hellR
  have hgcd : Nat.gcd cp R = 1 := hunit
  rw [hgcd] at hellgcd
  have helleq : ell = 1 := Nat.dvd_one.mp hellgcd
  omega

def SampleSuppliesUnit (h N Q R : ℕ) : Prop :=
  ∃ sample : Finset ℕ,
    (∀ cp ∈ sample,
      ∃ c : ℕ, ∃ z : ℤ, GoodFirst (h * N) (h * Q) c cp z) ∧
    ∃ cp ∈ sample, Nat.Coprime cp R

theorem no_finite_good_sample_supplies_unit
    {h N Q ell R : ℕ}
    (hh : 0 < h) (hQ : 0 < Q) (hQlt : Q < 20)
    (hcop : Nat.Coprime N Q)
    (hell : 1 < ell) (hellN : ell ∣ N) (hellR : ell ∣ R) :
    ¬ SampleSuppliesUnit h N Q R := by
  rintro ⟨sample, hgood, cp, hmem, hunit⟩
  obtain ⟨c, z, hg⟩ := hgood cp hmem
  exact no_good_unit_of_common_factor
    hh hQ hQlt hcop hell hellN hellR hg hunit

theorem original_instance_is_a_family_member :
    ¬ SampleSuppliesUnit 6006 16 17 32 := by
  exact no_finite_good_sample_supplies_unit
    (ell := 2) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num) (by norm_num)

#print axioms good_residue_zero
#print axioms good_first_iff_exact_lattice
#print axioms no_good_unit_of_common_factor
#print axioms no_finite_good_sample_supplies_unit
#print axioms original_instance_is_a_family_member

end ShorWindowFamily
