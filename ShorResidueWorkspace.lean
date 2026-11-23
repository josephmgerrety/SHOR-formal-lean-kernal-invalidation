import Mathlib
import LeanFiberFourier

namespace ShorResidueWorkspace

open scoped BigOperators
open LeanFiberFourier

/-- A balanced label map has exactly m inputs in each label fiber. -/
def BalancedLabels {n d : ℕ} [NeZero n]
    (label : ZMod n → Fin d) (m : ℕ) : Prop :=
  ∀ i : Fin d, (Finset.univ.filter (fun b => label b = i)).card = m

/-- Count the squared distances from one orthogonal label to every label. -/
theorem balanced_label_distance_sum
    {n d : ℕ} [NeZero n] (m : ℕ)
    (label : ZMod n → Fin d) (hbalanced : BalancedLabels label m)
    (b : ZMod n) :
    (∑ b' : ZMod n, if label b = label b' then (0 : ℝ) else 2) =
      2 * ((n : ℝ) - m) := by
  classical
  have heq : (∑ b' : ZMod n,
      if label b = label b' then (2 : ℝ) else 0) = 2 * (m : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun b' => label b = label b')).card = m := by
      simpa only [eq_comm] using hbalanced (label b)
    rw [hcard]
    ring
  have hterm (b' : ZMod n) :
      (if label b = label b' then (0 : ℝ) else 2) =
        2 - (if label b = label b' then (2 : ℝ) else 0) := by
    by_cases h : label b = label b' <;> simp only [h, ite_true, ite_false] <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, heq]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- Balanced orthogonal labels determine the complete fiber variance by counting. -/
theorem balanced_workspace_variance
    {n d : ℕ} [NeZero n] (m : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (label : ZMod n → Fin d) (hbalanced : BalancedLabels label m)
    (hdistance : ∀ t b b',
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2 =
        if label b = label b' then (0 : ℝ) else 2) :
    (∑ t : ZMod n, ∑ b : ZMod n, ∑ b' : ZMod n,
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2) =
      2 * (n : ℝ) ^ 2 * ((n : ℝ) - m) := by
  simp_rw [hdistance, balanced_label_distance_sum m label hbalanced]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- The balanced label count gives the exact 1 - 1/d variance expression. -/
theorem balanced_workspace_variance_fraction
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (label : ZMod n → Fin d) (hbalanced : BalancedLabels label m)
    (hdistance : ∀ t b b',
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2 =
        if label b = label b' then (0 : ℝ) else 2) :
    (∑ t : ZMod n, ∑ b : ZMod n, ∑ b' : ZMod n,
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2) =
      2 * (n : ℝ) ^ 3 * (1 - 1 / (d : ℝ)) := by
  rw [balanced_workspace_variance m e k label hbalanced hdistance]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hnR : (n : ℝ) = (d : ℝ) * m := by exact_mod_cast hn
  rw [hnR]
  field_simp

/-- The Fourier line survival is 1/d for balanced orthogonal workspace labels. -/
theorem balanced_workspace_line_defect_and_survival
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1)
    (label : ZMod n → Fin d) (hbalanced : BalancedLabels label m)
    (hdistance : ∀ t b b',
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2 =
        if label b = label b' then (0 : ℝ) else 2) :
    1 - (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      1 - 1 / (d : ℝ) ∧
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      1 / (d : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hdef := exact_fourier_line_defect e k hunit
  rw [balanced_workspace_variance_fraction m hd hn e k label hbalanced hdistance]
    at hdef
  have hcancel :
      2 * (n : ℝ) ^ 3 * (1 - 1 / (d : ℝ)) / (2 * (n : ℝ) ^ 3) =
      1 - 1 / (d : ℝ) := by field_simp
  rw [hcancel] at hdef
  exact ⟨hdef, by linarith⟩

/-- Specialize the counted balanced-label theorem to 2^r labels. -/
theorem two_adic_balanced_workspace_survival
    {n : ℕ} [NeZero n] (r m : ℕ) (hn : n = 2 ^ r * m)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : ZMod n → ZMod n → E) (k : ZMod n)
    (hunit : ∀ a b, ‖e a b‖ = 1)
    (label : ZMod n → Fin (2 ^ r)) (hbalanced : BalancedLabels label m)
    (hdistance : ∀ t b b',
      ‖e (t + k * b) b - e (t + k * b') b'‖ ^ 2 =
        if label b = label b' then (0 : ℝ) else 2) :
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar e k u (-(k * u)) t‖ ^ 2) =
      1 / (2 : ℝ) ^ r := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (balanced_workspace_line_defect_and_survival m (pow_pos (by norm_num) r)
      hn e k hunit label hbalanced hdistance).2

/-- An explicit workspace stores the label in a canonical orthonormal basis. -/
def labelWorkspace {𝕜 : Type*} [RCLike 𝕜] {n d : ℕ} (label : ZMod n → Fin d)
    (_a b : ZMod n) : EuclideanSpace 𝕜 (Fin d) :=
  EuclideanSpace.single (label b) 1

theorem label_workspace_norm {n d : ℕ} (label : ZMod n → Fin d)
    (a b : ZMod n) : ‖labelWorkspace (𝕜 := ℂ) label a b‖ = 1 := by
  simp [labelWorkspace, EuclideanSpace.single, PiLp.norm_single]

theorem label_workspace_distance {n d : ℕ} (label : ZMod n → Fin d)
    (k t b b' : ZMod n) :
    ‖labelWorkspace (𝕜 := ℂ) label (t + k * b) b -
      labelWorkspace (𝕜 := ℂ) label (t + k * b') b'‖ ^ 2 =
      if label b = label b' then (0 : ℝ) else 2 := by
  by_cases h : label b = label b'
  · simp [labelWorkspace, h]
  · rw [norm_sub_sq (𝕜 := ℂ)]
    norm_num [labelWorkspace, EuclideanSpace.single, PiLp.norm_single,
      EuclideanSpace.inner_single_left, h]

/-- No abstract distance law is assumed for the canonical label workspace. -/
theorem canonical_label_workspace_survival
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m)
    (label : ZMod n → Fin d) (hbalanced : BalancedLabels label m) (k : ZMod n) :
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar (labelWorkspace (𝕜 := ℂ) label) k u (-(k * u)) t‖ ^ 2) =
      1 / (d : ℝ) := by
  exact (balanced_workspace_line_defect_and_survival m hd hn
    (labelWorkspace (𝕜 := ℂ) label) k (label_workspace_norm label) label hbalanced
    (label_workspace_distance label k)).2

/-- The canonical remainder gives an executable residue label. -/
def residueLabel {n d : ℕ} (hd : 0 < d) (b : ZMod n) : Fin d :=
  ⟨b.val % d, Nat.mod_lt _ hd⟩

/-- Each residue appears m times in ZMod (d*m). -/
theorem residue_labels_balanced
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m) :
    BalancedLabels (residueLabel (n := n) hd) m := by
  classical
  intro i
  let f : Fin m → ZMod n := fun j => ((d * j.val + i.val : ℕ) : ZMod n)
  have hlt (j : Fin m) : d * j.val + i.val < n := by
    rw [hn]
    calc
      d * j.val + i.val < d * j.val + d := Nat.add_lt_add_left i.isLt _
      _ = d * (j.val + 1) := by ring
      _ ≤ d * m := Nat.mul_le_mul_left d (by omega)
  have hval (j : Fin m) : (f j).val = d * j.val + i.val := by
    exact ZMod.val_natCast_of_lt (hlt j)
  have hinj : Function.Injective f := by
    intro j j' heq
    have hv := congrArg ZMod.val heq
    rw [hval, hval] at hv
    have heqmul : d * j.val = d * j'.val := Nat.add_right_cancel hv
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hd heqmul)
  have hset : Finset.univ.filter (fun b : ZMod n => residueLabel hd b = i) =
      Finset.univ.image f := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hb
      have hrem : b.val % d = i.val := congrArg Fin.val hb
      have hj : b.val / d < m := by
        apply (Nat.div_lt_iff_lt_mul hd).mpr
        simpa only [hn, Nat.mul_comm d m] using b.val_lt
      refine ⟨⟨b.val / d, hj⟩, ?_⟩
      apply ZMod.val_injective n
      rw [hval]
      change d * (b.val / d) + i.val = b.val
      rw [← hrem, Nat.add_comm]
      exact Nat.mod_add_div b.val d
    · rintro ⟨j, rfl⟩
      apply Fin.ext
      change (f j).val % d = i.val
      rw [hval]
      simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt i.isLt]
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The variance formula now follows from the explicit residue workspace alone. -/
theorem residue_workspace_variance
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m) (k : ZMod n) :
    (∑ t : ZMod n, ∑ b : ZMod n, ∑ b' : ZMod n,
      ‖labelWorkspace (𝕜 := ℂ) (residueLabel hd) (t + k * b) b -
        labelWorkspace (𝕜 := ℂ) (residueLabel hd) (t + k * b') b'‖ ^ 2) =
      2 * (n : ℝ) ^ 3 * (1 - 1 / (d : ℝ)) := by
  exact balanced_workspace_variance_fraction m hd hn
    (labelWorkspace (𝕜 := ℂ) (residueLabel hd)) k (residueLabel hd)
    (residue_labels_balanced m hd hn) (label_workspace_distance _ k)

/-- Storing b modulo d in an orthonormal workspace leaves exactly 1/d on the line. -/
theorem residue_workspace_line_survival
    {n d : ℕ} [NeZero n] (m : ℕ) (hd : 0 < d) (hn : n = d * m) (k : ZMod n) :
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar (labelWorkspace (𝕜 := ℂ) (residueLabel hd))
        k u (-(k * u)) t‖ ^ 2) = 1 / (d : ℝ) := by
  exact canonical_label_workspace_survival m hd hn (residueLabel hd)
    (residue_labels_balanced m hd hn) k

/-- The explicit 2-adic residue workspace has line survival 2^(-r). -/
theorem two_adic_residue_workspace_line_survival
    {n : ℕ} [NeZero n] (r m : ℕ) (hn : n = 2 ^ r * m) (k : ZMod n) :
    let hd : 0 < 2 ^ r := pow_pos (by norm_num) r
    (∑ u : ZMod n, ∑ t : ZMod n,
      ‖amplitude ZMod.stdAddChar (labelWorkspace (𝕜 := ℂ) (residueLabel hd))
        k u (-(k * u)) t‖ ^ 2) = 1 / (2 : ℝ) ^ r := by
  dsimp only
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    residue_workspace_line_survival m (pow_pos (by norm_num) r) hn k
#print axioms balanced_label_distance_sum
#print axioms balanced_workspace_variance
#print axioms balanced_workspace_variance_fraction
#print axioms balanced_workspace_line_defect_and_survival
#print axioms two_adic_balanced_workspace_survival
#print axioms label_workspace_norm
#print axioms label_workspace_distance
#print axioms canonical_label_workspace_survival
#print axioms residue_labels_balanced
#print axioms residue_workspace_variance
#print axioms residue_workspace_line_survival
#print axioms two_adic_residue_workspace_line_survival

end ShorResidueWorkspace
