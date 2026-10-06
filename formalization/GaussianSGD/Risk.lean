import GaussianSGD.Comparison
import GaussianSGD.SmallBall
import GaussianSGD.Kernel

/-!
# Risk controlled by kernel correlation (`thm:risk`)

The conditional bound given a hidden layer in the good event, and the averaged
bound over the Gaussian initialization.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Risk controlled by kernel correlation (`thm:risk`), conditional on a hidden layer
in the good event. -/
theorem cond_risk_lower {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (W : Fin m → Vec n) (hG : Good W)
    (h : Cube n → Bool) (D : Dist n) :
    ENNReal.ofReal (1 / 2 - rhoA m - 24 * kappa n m - 27 * (η * m * T) / Real.sqrt T
        - 9 * (η * m * T) * ‖mu (psi W) h D‖)
      ≤ ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) := by
  sorry

/-- Risk controlled by kernel correlation (`thm:risk`). -/
theorem risk_lower_bound {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (h : Cube n → Bool) (D : Dist n) :
    ENNReal.ofReal (1 / 2 - lossTerm n m T (η * m * T) - 9 * (η * m * T) * kernelCorr h D)
      ≤ risk m η T h D := by
  sorry

end GaussianSGD
