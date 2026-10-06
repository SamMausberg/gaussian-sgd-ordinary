import GaussianSGD.Defs

/-!
# Definitions for the fixed-gate regime (`thm:gate`)
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Gated-coordinate features `φ_{W₀}(x)_{j,i} = x_i 1{⟪w₀ⱼ, x⟫ > 0}`. -/
def gateFeat {n m : ℕ} (W : Fin m → Vec n) (x : Cube n) : EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun p => bsign (x p.2) * if 0 < ⟪W p.1, pt x⟫ then 1 else 0)

/-- Row radius `r_j = |a₀ⱼ| sinh τ + ‖w₀ⱼ‖ (cosh τ - 1)`. -/
def gateRadius {n m : ℕ} (τ : ℝ) (θ0 : Params n m) (j : Fin m) : ℝ :=
  |θ0.2 j| * Real.sinh τ + ‖θ0.1 j‖ * (Real.cosh τ - 1)

/-- The exceptional set `𝔅 = ⋃ⱼ {x : |⟪w₀ⱼ, x⟫| ≤ √n rⱼ}`. -/
def gateSet {n m : ℕ} (τ : ℝ) (θ0 : Params n m) : Set (Cube n) :=
  {x | ∃ j, |⟪θ0.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ0 j}

/-- The trained coefficient array `C_{ji} = q⁻¹ ∑_{t ∈ I_T} a_{tj} (W_t)_{ji}`. -/
def gateCoeff {n m : ℕ} (η : ℝ) (T : ℕ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun p => ((tail T).card : ℝ)⁻¹ *
    ∑ t ∈ tail T, (traj η θ0 xs ys t).2 p.1 * (traj η θ0 xs ys t).1 p.1 p.2)

/-- The bound `B_{n,m}(τ)` on the expected mass of the exceptional set. -/
def gateBound (n m : ℕ) (τ : ℝ) : ℝ :=
  min 1 ((2 / Real.pi * Real.sqrt (n * m) * Real.sinh τ +
      Real.sqrt (2 / Real.pi) * m * Real.sqrt (n - 1) * (Real.cosh τ - 1)) / (2 - Real.cosh τ))

end GaussianSGD
