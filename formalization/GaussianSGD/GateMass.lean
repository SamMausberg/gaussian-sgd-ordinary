import GaussianSGD.GateDefs
import GaussianSGD.Init

/-!
# Expected mass of the exceptional set in the fixed-gate regime (`thm:gate`)

For a fixed marginal, the set of cube points at which some gate might change has expected
mass at most `B_{n,m}(τ)` under the Gaussian initialization.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Fixed-gate regime (`thm:gate`), Gaussian estimate: `E_{W₀,a₀} D(𝔅) ≤ B_{n,m}(τ)` for every fixed marginal. -/
theorem gateSet_mass {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) (D : Dist n) :
    ∫⁻ W, ∫⁻ a, ENNReal.ofReal (∑ x, D.p x * (gateSet τ (W, a)).indicator 1 x)
        ∂(outLaw m) ∂(hiddenLaw n m) ≤ ENNReal.ofReal (gateBound n m τ) := by
  sorry

/-- Fixed-gate regime (`thm:gate`), the simplified bound `B_{n,m}(τ) ≤ 2√(nm) τ + m√n τ²` for `0 ≤ τ ≤ 1`. -/
theorem gateBound_le {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) :
    gateBound n m τ ≤ 2 * Real.sqrt (n * m) * τ + m * Real.sqrt n * τ ^ 2 := by
  sorry

end GaussianSGD
