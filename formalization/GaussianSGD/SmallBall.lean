import GaussianSGD.Density
import GaussianSGD.Population

/-!
# Anti-concentration of the symmetric tail (`lem:smallball`)

For every cube point the symmetric tail score has small-ball probability at most
`24 r` under the standard Gaussian initialization, and its sign has expected
error exactly `1/2` against every Boolean target.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Anti-concentration of the symmetric tail (`lem:smallball`), small-ball bound. -/
theorem smallball {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m)
    (hψ : ∀ x, 7 / 16 ≤ ‖ψ x‖ ^ 2 ∧ ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (x : Cube n)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Vec m) {b | |Zsym γ ψ D T x b| ≤ r} ≤ ENNReal.ofReal (24 * r) := by
  sorry

/-- Anti-concentration of the symmetric tail (`lem:smallball`): the symmetric classifier
has expected error exactly `1/2`. -/
theorem null_risk {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m)
    (hψ : ∀ x, 7 / 16 ≤ ‖ψ x‖ ^ 2 ∧ ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (h : Cube n → Bool) :
    ∫ b, err D (fun x => sgn (Zsym γ ψ D T x b)) h ∂(stdGaussian (Vec m)) = 1 / 2 := by
  sorry

end GaussianSGD
