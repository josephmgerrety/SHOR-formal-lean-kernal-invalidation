import LeanMeasurementNoGo
import LeanGraphCopies

namespace ShorFiniteCopyNoGo

open scoped BigOperators Matrix ComplexOrder
open Matrix WithLp
open LeanMeasurementNoGo ShorGraphCopies

theorem no_perfect_measurement_on_graph_copies
    (n t : ℕ) [NeZero n] (hn : 1 < n) :
    ¬ ∃ M : FinitePOVM (Basis n t) (ZMod n),
      PerfectlyDistinguishes M (graphVector (𝕜 := ℂ) n t) := by
  let : Fact (1 < n) := ⟨hn⟩
  exact no_perfect_povm_of_nonzero_inner
    (graphVector (𝕜 := ℂ) n t)
    (k := 0) (l := 1) zero_ne_one
    (graphVector_inner_ne_zero n t 0 1)

theorem no_perfect_decoded_measurement_on_graph_copies
    (n t : ℕ) [NeZero n] (hn : 1 < n)
    (O : Type*) [Fintype O] :
    ¬ ∃ (M : FinitePOVM (Basis n t) O) (decode : O → ZMod n),
      ∀ k l,
        (∑ o, if decode o = l then
          star (ofLp (graphVector (𝕜 := ℂ) n t k)) ⬝ᵥ
            (M.effect o *ᵥ ofLp (graphVector (𝕜 := ℂ) n t k)) else 0) =
        if k = l then 1 else 0 := by
  let : Fact (1 < n) := ⟨hn⟩
  exact no_perfect_decoded_povm_of_nonzero_inner
    (graphVector (𝕜 := ℂ) n t)
    (k := 0) (l := 1) zero_ne_one
    (graphVector_inner_ne_zero n t 0 1)

theorem normalized_states_and_no_perfect_measurement
    (n t : ℕ) [NeZero n] (hn : 1 < n) :
    (∀ k : ZMod n, ‖graphVector (𝕜 := ℂ) n t k‖ = 1) ∧
    ¬ ∃ M : FinitePOVM (Basis n t) (ZMod n),
      PerfectlyDistinguishes M (graphVector (𝕜 := ℂ) n t) := by
  exact ⟨graphVector_norm n t, no_perfect_measurement_on_graph_copies n t hn⟩

/-- Only n>1 and a finite natural copy count are needed. -/
theorem every_group_order_and_finite_copy_count
    (n t : ℕ) (hn : 1 < n) :
    letI : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
    (∀ k : ZMod n, ‖graphVector (𝕜 := ℂ) n t k‖ = 1) ∧
    ¬ ∃ M : FinitePOVM (Basis n t) (ZMod n),
      PerfectlyDistinguishes M (graphVector (𝕜 := ℂ) n t) := by
  let : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  exact normalized_states_and_no_perfect_measurement n t hn

#print axioms no_perfect_measurement_on_graph_copies
#print axioms no_perfect_decoded_measurement_on_graph_copies
#print axioms normalized_states_and_no_perfect_measurement
#print axioms every_group_order_and_finite_copy_count

end ShorFiniteCopyNoGo
