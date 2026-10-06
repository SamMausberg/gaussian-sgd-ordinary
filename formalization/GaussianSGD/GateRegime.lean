import GaussianSGD.Init

/-!
# The fixed-gate regime (`thm:gate`)

For a small total step, every gate at a cube point outside an initialization-defined
set keeps its initial sign along every labeled history. Outside that set the tail score
is exactly linear in the `mn` initial gated-coordinate features, and the set has small
expected mass under every fixed marginal. This yields a probabilistic-dimension bound.
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

/-- Fixed-gate regime (`thm:gate`), Gaussian estimate: `E_{W₀,a₀} D(𝔅) ≤ B_{n,m}(τ)` for every fixed marginal. -/
theorem gateSet_mass {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) (D : Dist n) :
    ∫⁻ W, ∫⁻ a, ENNReal.ofReal (∑ x, D.p x * (gateSet τ (W, a)).indicator 1 x)
        ∂(outLaw m) ∂(hiddenLaw n m) ≤ ENNReal.ofReal (gateBound n m τ) := by
  sorry

/-- Fixed-gate regime (`thm:gate`), the simplified bound `B_{n,m}(τ) ≤ 2√(nm) τ + m√n τ²` for `0 ≤ τ ≤ 1`. -/
theorem gateBound_le {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) :
    gateBound n m τ ≤ 2 * Real.sqrt (n * m) * τ + m * Real.sqrt n * τ ^ 2 := by
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
