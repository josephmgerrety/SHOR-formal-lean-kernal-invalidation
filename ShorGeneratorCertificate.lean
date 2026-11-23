import Mathlib

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace ShorGenerator

theorem p_prime : Nat.Prime 96097 := by
  norm_num

theorem fifth_power_target :
    (5 : ZMod 96097) ^ 22 = 78073 := by
  decide

theorem full_power :
    (5 : ZMod 96097) ^ 96096 = 1 := by
  let : Fact (Nat.Prime 96097) := ⟨p_prime⟩
  simpa using (ZMod.pow_card_sub_one_eq_one
    (a := (5 : ZMod 96097)) (by decide))

private theorem square_1 :
    (5 : ZMod 96097) ^ 2 = 25 := by
  decide

private theorem square_2 :
    (5 : ZMod 96097) ^ 4 = 625 := by
  calc
    (5 : ZMod 96097) ^ 4 =
        ((5 : ZMod 96097) ^ 2) ^ 2 := by
          simp only [show 4 = 2 * 2 by norm_num, pow_mul]
    _ = 625 := by
      rw [square_1]
      decide

private theorem square_3 :
    (5 : ZMod 96097) ^ 8 = 6237 := by
  calc
    (5 : ZMod 96097) ^ 8 =
        ((5 : ZMod 96097) ^ 4) ^ 2 := by
          simp only [show 8 = 4 * 2 by norm_num, pow_mul]
    _ = 6237 := by
      rw [square_2]
      decide

private theorem square_4 :
    (5 : ZMod 96097) ^ 16 = 76981 := by
  calc
    (5 : ZMod 96097) ^ 16 =
        ((5 : ZMod 96097) ^ 8) ^ 2 := by
          simp only [show 16 = 8 * 2 by norm_num, pow_mul]
    _ = 76981 := by
      rw [square_3]
      decide

private theorem square_5 :
    (5 : ZMod 96097) ^ 32 = 60662 := by
  calc
    (5 : ZMod 96097) ^ 32 =
        ((5 : ZMod 96097) ^ 16) ^ 2 := by
          simp only [show 32 = 16 * 2 by norm_num, pow_mul]
    _ = 60662 := by
      rw [square_4]
      decide

private theorem square_6 :
    (5 : ZMod 96097) ^ 64 = 35823 := by
  calc
    (5 : ZMod 96097) ^ 64 =
        ((5 : ZMod 96097) ^ 32) ^ 2 := by
          simp only [show 64 = 32 * 2 by norm_num, pow_mul]
    _ = 35823 := by
      rw [square_5]
      decide

private theorem square_7 :
    (5 : ZMod 96097) ^ 128 = 7991 := by
  calc
    (5 : ZMod 96097) ^ 128 =
        ((5 : ZMod 96097) ^ 64) ^ 2 := by
          simp only [show 128 = 64 * 2 by norm_num, pow_mul]
    _ = 7991 := by
      rw [square_6]
      decide

private theorem square_8 :
    (5 : ZMod 96097) ^ 256 = 47673 := by
  calc
    (5 : ZMod 96097) ^ 256 =
        ((5 : ZMod 96097) ^ 128) ^ 2 := by
          simp only [show 256 = 128 * 2 by norm_num, pow_mul]
    _ = 47673 := by
      rw [square_7]
      decide

private theorem square_9 :
    (5 : ZMod 96097) ^ 512 = 20879 := by
  calc
    (5 : ZMod 96097) ^ 512 =
        ((5 : ZMod 96097) ^ 256) ^ 2 := by
          simp only [show 512 = 256 * 2 by norm_num, pow_mul]
    _ = 20879 := by
      rw [square_8]
      decide

private theorem square_10 :
    (5 : ZMod 96097) ^ 1024 = 36649 := by
  calc
    (5 : ZMod 96097) ^ 1024 =
        ((5 : ZMod 96097) ^ 512) ^ 2 := by
          simp only [show 1024 = 512 * 2 by norm_num, pow_mul]
    _ = 36649 := by
      rw [square_9]
      decide

private theorem square_11 :
    (5 : ZMod 96097) ^ 2048 = 1432 := by
  calc
    (5 : ZMod 96097) ^ 2048 =
        ((5 : ZMod 96097) ^ 1024) ^ 2 := by
          simp only [show 2048 = 1024 * 2 by norm_num, pow_mul]
    _ = 1432 := by
      rw [square_10]
      decide

private theorem square_12 :
    (5 : ZMod 96097) ^ 4096 = 32587 := by
  calc
    (5 : ZMod 96097) ^ 4096 =
        ((5 : ZMod 96097) ^ 2048) ^ 2 := by
          simp only [show 4096 = 2048 * 2 by norm_num, pow_mul]
    _ = 32587 := by
      rw [square_11]
      decide

private theorem square_13 :
    (5 : ZMod 96097) ^ 8192 = 40719 := by
  calc
    (5 : ZMod 96097) ^ 8192 =
        ((5 : ZMod 96097) ^ 4096) ^ 2 := by
          simp only [show 8192 = 4096 * 2 by norm_num, pow_mul]
    _ = 40719 := by
      rw [square_12]
      decide

private theorem square_14 :
    (5 : ZMod 96097) ^ 16384 = 75420 := by
  calc
    (5 : ZMod 96097) ^ 16384 =
        ((5 : ZMod 96097) ^ 8192) ^ 2 := by
          simp only [show 16384 = 8192 * 2 by norm_num, pow_mul]
    _ = 75420 := by
      rw [square_13]
      decide

private theorem square_15 :
    (5 : ZMod 96097) ^ 32768 = 2776 := by
  calc
    (5 : ZMod 96097) ^ 32768 =
        ((5 : ZMod 96097) ^ 16384) ^ 2 := by
          simp only [show 32768 = 16384 * 2 by norm_num, pow_mul]
    _ = 2776 := by
      rw [square_14]
      decide

theorem half_residue :
    (5 : ZMod 96097) ^ 48048 = 96096 := by
  calc
    (5 : ZMod 96097) ^ 48048 =
        ((5 : ZMod 96097) ^ 16) * ((5 : ZMod 96097) ^ 32) * ((5 : ZMod 96097) ^ 128) * ((5 : ZMod 96097) ^ 256) * ((5 : ZMod 96097) ^ 512) * ((5 : ZMod 96097) ^ 2048) * ((5 : ZMod 96097) ^ 4096) * ((5 : ZMod 96097) ^ 8192) * ((5 : ZMod 96097) ^ 32768) := by
          calc
            _ = (5 : ZMod 96097) ^ (16 + 32 + 128 + 256 + 512 + 2048 + 4096 + 8192 + 32768) := by congr 1
            _ = _ := by simp only [pow_add]
    _ = 96096 := by
      rw [square_4, square_5, square_7, square_8, square_9, square_11, square_12, square_13, square_15]
      decide

theorem half_power :
    (5 : ZMod 96097) ^ (96096 / 2) ≠ 1 := by
  rw [show 96096 / 2 = 48048 by norm_num]
  rw [half_residue]
  decide

theorem third_residue :
    (5 : ZMod 96097) ^ 32032 = 22527 := by
  calc
    (5 : ZMod 96097) ^ 32032 =
        ((5 : ZMod 96097) ^ 32) * ((5 : ZMod 96097) ^ 256) * ((5 : ZMod 96097) ^ 1024) * ((5 : ZMod 96097) ^ 2048) * ((5 : ZMod 96097) ^ 4096) * ((5 : ZMod 96097) ^ 8192) * ((5 : ZMod 96097) ^ 16384) := by
          calc
            _ = (5 : ZMod 96097) ^ (32 + 256 + 1024 + 2048 + 4096 + 8192 + 16384) := by congr 1
            _ = _ := by simp only [pow_add]
    _ = 22527 := by
      rw [square_5, square_8, square_10, square_11, square_12, square_13, square_14]
      decide

theorem third_power :
    (5 : ZMod 96097) ^ (96096 / 3) ≠ 1 := by
  rw [show 96096 / 3 = 32032 by norm_num]
  rw [third_residue]
  decide

theorem seventh_residue :
    (5 : ZMod 96097) ^ 13728 = 20929 := by
  calc
    (5 : ZMod 96097) ^ 13728 =
        ((5 : ZMod 96097) ^ 32) * ((5 : ZMod 96097) ^ 128) * ((5 : ZMod 96097) ^ 256) * ((5 : ZMod 96097) ^ 1024) * ((5 : ZMod 96097) ^ 4096) * ((5 : ZMod 96097) ^ 8192) := by
          calc
            _ = (5 : ZMod 96097) ^ (32 + 128 + 256 + 1024 + 4096 + 8192) := by congr 1
            _ = _ := by simp only [pow_add]
    _ = 20929 := by
      rw [square_5, square_7, square_8, square_10, square_12, square_13]
      decide

theorem seventh_power :
    (5 : ZMod 96097) ^ (96096 / 7) ≠ 1 := by
  rw [show 96096 / 7 = 13728 by norm_num]
  rw [seventh_residue]
  decide

theorem eleventh_residue :
    (5 : ZMod 96097) ^ 8736 = 74690 := by
  calc
    (5 : ZMod 96097) ^ 8736 =
        ((5 : ZMod 96097) ^ 32) * ((5 : ZMod 96097) ^ 512) * ((5 : ZMod 96097) ^ 8192) := by
          calc
            _ = (5 : ZMod 96097) ^ (32 + 512 + 8192) := by congr 1
            _ = _ := by simp only [pow_add]
    _ = 74690 := by
      rw [square_5, square_9, square_13]
      decide

theorem eleventh_power :
    (5 : ZMod 96097) ^ (96096 / 11) ≠ 1 := by
  rw [show 96096 / 11 = 8736 by norm_num]
  rw [eleventh_residue]
  decide

theorem thirteenth_residue :
    (5 : ZMod 96097) ^ 7392 = 67413 := by
  calc
    (5 : ZMod 96097) ^ 7392 =
        ((5 : ZMod 96097) ^ 32) * ((5 : ZMod 96097) ^ 64) * ((5 : ZMod 96097) ^ 128) * ((5 : ZMod 96097) ^ 1024) * ((5 : ZMod 96097) ^ 2048) * ((5 : ZMod 96097) ^ 4096) := by
          calc
            _ = (5 : ZMod 96097) ^ (32 + 64 + 128 + 1024 + 2048 + 4096) := by congr 1
            _ = _ := by simp only [pow_add]
    _ = 67413 := by
      rw [square_5, square_6, square_7, square_10, square_11, square_12]
      decide

theorem thirteenth_power :
    (5 : ZMod 96097) ^ (96096 / 13) ≠ 1 := by
  rw [show 96096 / 13 = 7392 by norm_num]
  rw [thirteenth_residue]
  decide

theorem generator_order :
    orderOf (5 : ZMod 96097) = 96096 := by
  apply orderOf_eq_of_pow_and_pow_div_prime full_power
  intro r hr hdiv
  have hfactor : r ∣ 2^5 * 3 * 7 * 11 * 13 := by
    simpa only [show (96096 : Nat) =
      2^5 * 3 * 7 * 11 * 13 by norm_num] using hdiv
  simp only [Nat.Prime.dvd_mul hr] at hfactor
  have hrs : r = 2 ∨ r = 3 ∨ r = 7 ∨
      r = 11 ∨ r = 13 := by
    rcases hfactor with hleft | h13
    · rcases hleft with hleft | h11
      · rcases hleft with hleft | h7
        · rcases hleft with h2 | h3
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr
              (by norm_num)).mp (hr.dvd_of_dvd_pow h2))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr
              (by norm_num)).mp h3))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr
            (by norm_num)).mp h7)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h11))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h13))))
  rcases hrs with rfl | rfl | rfl | rfl | rfl
  · simpa using half_power
  · simpa using third_power
  · simpa using seventh_power
  · simpa using eleventh_power
  · simpa using thirteenth_power

#print axioms p_prime
#print axioms fifth_power_target
#print axioms generator_order

end ShorGenerator



