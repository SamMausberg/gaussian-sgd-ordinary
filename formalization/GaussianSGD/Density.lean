import GaussianSGD.Defs

/-!
# Density at the beginning of the tail (`lem:density`)

Started from a standard Gaussian vector, the label-symmetric recurrence at time
`s = ⌈T/2⌉` has law at most `e` times the standard Gaussian law. Equivalently, its
density is at most `e (2π)^{-m/2} exp(-‖v‖²/2)`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Density at the beginning of the tail (`lem:density`). -/
theorem density_bound {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) :
    (stdGaussian (Vec m)).map ((Rmap γ ψ D)^[(T + 1) / 2])
      ≤ ENNReal.ofReal (Real.exp 1) • stdGaussian (Vec m) := by
  sorry

end GaussianSGD
