import GaussianSGD.Defs

/-!
# Initialization bounds (`lem:init`)
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

instance isProbabilityMeasure_rowLaw (n : ℕ) : IsProbabilityMeasure (rowLaw n) := by
  unfold rowLaw; infer_instance

instance isProbabilityMeasure_hiddenLaw (n m : ℕ) : IsProbabilityMeasure (hiddenLaw n m) := by
  unfold hiddenLaw; infer_instance

instance isProbabilityMeasure_outLaw (m : ℕ) : IsProbabilityMeasure (outLaw m) := by
  unfold outLaw; infer_instance

/-- Initialization bounds (`lem:init`), hidden layer: `Pr(W₀ ∉ 𝒢) ≤ ρ_W`. -/
theorem init_hidden {n m : ℕ} (hn : 1 ≤ n) :
    hiddenLaw n m {W | ¬ Good W} ≤ ENNReal.ofReal (rhoW n m) := by
  sorry

/-- Initialization bounds (`lem:init`), output layer: `Pr(‖a₀‖ > 2) ≤ ρ_a`. -/
theorem init_output (m : ℕ) : outLaw m {a | 2 < ‖a‖} ≤ ENNReal.ofReal (rhoA m) := by
  sorry

end GaussianSGD
