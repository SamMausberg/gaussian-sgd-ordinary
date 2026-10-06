import GaussianSGD.GateMass

/-!
# The fixed-gate regime (`thm:gate`)

For a small total step, every gate at a cube point outside an initialization-defined set keeps
its initial sign along every labeled history. Outside that set the tail score is exactly linear
in the `mn` initial gated-coordinate features, and the set has small expected mass under every
fixed marginal. This yields a probabilistic-dimension bound.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Row movement (`lem:rows`), for every labeled history with `|y_t| ≤ 1`. -/
theorem row_movement {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (θ0 : Params n m) (xs : ℕ → Cube n)
    (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (j : Fin m) (t : ℕ) :
    |(traj η θ0 xs ys t).2 j| ≤
        |θ0.2 j| * Real.cosh (t * η * Real.sqrt n) + ‖θ0.1 j‖ * Real.sinh (t * η * Real.sqrt n) ∧
    ‖(traj η θ0 xs ys t).1 j - θ0.1 j‖ ≤
        |θ0.2 j| * Real.sinh (t * η * Real.sqrt n) +
          ‖θ0.1 j‖ * (Real.cosh (t * η * Real.sqrt n) - 1) := by
  sorry

/-- Fixed-gate regime (`thm:gate`), exact representation: outside `𝔅`, for every labeled history, the
tail score equals `⟪C, φ_{W₀}(x)⟫`. -/
theorem exact_representation {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (T : ℕ) (θ0 : Params n m)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (x : Cube n)
    (hx : x ∉ gateSet (η * T * Real.sqrt n) θ0) :
    tailScore η T θ0 xs ys x = ⟪gateCoeff η T θ0 xs ys, gateFeat θ0.1 x⟫ := by
  sorry

/-- Fixed-gate regime (`thm:gate`), probabilistic dimension: if the process learns every target in `H` to
expected error `ε` under every marginal and `τ = η T √n ≤ 1`, the law of `φ_{W₀}`
witnesses `pdc_{ε + B_{n,m}(τ)}(H) ≤ mn`. -/
theorem gate_pdc {n m T : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 ≤ η)
    (hτ : η * T * Real.sqrt n ≤ 1) (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    ∀ h ∈ H, ∀ D : Dist n,
      ∫⁻ W, ENNReal.ofReal
          (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h)
        ∂(hiddenLaw n m) ≤ ENNReal.ofReal (ε + gateBound n m (η * T * Real.sqrt n)) := by
  sorry

/-- Fixed-gate regime (`thm:gate`), small-step form: `η ≤ 1/m` and `m ≥ 16 n² T² / δ²` give
`pdc_{ε + δ}(H) ≤ mn`. -/
theorem gate_small_step {n m T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / m) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1) (hm : 16 * n ^ 2 * T ^ 2 / δ ^ 2 ≤ m)
    (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    ∀ h ∈ H, ∀ D : Dist n,
      ∫⁻ W, ENNReal.ofReal
          (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h)
        ∂(hiddenLaw n m) ≤ ENNReal.ofReal (ε + δ) := by
  sorry

end GaussianSGD
