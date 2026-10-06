import GaussianSGD.Risk
import GaussianSGD.Geometry

/-!
# Kernel margin from every marginal (`thm:margin`) and corollaries

All-marginal success forces a Gaussian ReLU kernel margin and bounds the VC
dimension. The section also records the explicit sufficient conditions on
`m` and `T`, the numerical instance `m ≥ 2^20 n`, `T ≥ 2^24`, and the parity bound.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Kernel margin from every marginal (`thm:margin`): margin and VC parts. -/
theorem kernel_margin {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (H : Finset (Cube n → Bool))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε)
    (hΔ : lossTerm n m T (η * m * T) ≤ (1 / 2 - ε) / 2) :
    (∀ h ∈ H, ∀ D : Dist n, (1 / 2 - ε) / (18 * (η * m * T)) ≤ kernelCorr h D) ∧
    (∀ h ∈ H, ∃ u : Lp ℝ 2 (rowLaw n), ‖u‖ = 1 ∧
        ∀ x, (1 / 2 - ε) / (18 * (η * m * T)) ≤ bsign (h x) * ⟪u, Phi x⟫) ∧
    (∀ S : Finset (Cube n), Shatters H S →
        (S.card : ℝ) ≤ 162 * (η * m * T) ^ 2 / (1 / 2 - ε) ^ 2) := by
  sorry

/-- Explicit sufficient conditions for `Δ ≤ θ/2` (`thm:margin`). -/
theorem lossTerm_le_half {n m T : ℕ} (hn : 1 ≤ n) {B θ : ℝ} (hB : 0 < B) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (hm : 2 ^ 17 * (n : ℝ) / θ ≤ m) (hT : (216 * B / θ) ^ 2 ≤ T) :
    lossTerm n m T B ≤ θ / 2 := by
  sorry

/-- The numerical instance: `m ≥ 2^20 n`, `T ≥ 2^24`, `B ≤ 12` give `Δ ≤ 471/4096 < 1/8`. -/
theorem lossTerm_regime {n m T : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB0 : 0 < B) (hB : B ≤ 12)
    (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T) :
    lossTerm n m T B ≤ 471 / 4096 := by
  sorry

/-- `thm:risk` in the numerical regime: `Risk(h,D) ≥ 3/8 - 9 B A_D(h)`. -/
theorem risk_lower_bound_regime {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m)
    (hT : 2 ^ 24 ≤ T) {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (h : Cube n → Bool)
    (D : Dist n) :
    ENNReal.ofReal (3 / 8 - 9 * (η * m * T) * kernelCorr h D) ≤ risk m η T h D := by
  sorry

/-- `thm:margin` in the numerical regime with error below `1/4`: margin `1/(72B)` and
`VC(H) ≤ 2592 B²`. -/
theorem kernel_margin_regime {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T)
    {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hε : ε < 1 / 4) (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    (∀ h ∈ H, ∃ u : Lp ℝ 2 (rowLaw n), ‖u‖ = 1 ∧
        ∀ x, 1 / (72 * (η * m * T)) ≤ bsign (h x) * ⟪u, Phi x⟫) ∧
    (∀ S : Finset (Cube n), Shatters H S → (S.card : ℝ) ≤ 2592 * (η * m * T) ^ 2) := by
  sorry

/-- Parity obstruction (`cor:parity`). -/
theorem parity_lower_bound {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T)
    {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (A : Finset (Fin n)) :
    ENNReal.ofReal (3 / 8 - 9 * (η * m * T) / Real.sqrt (2 * (n.choose A.card)))
      ≤ risk m η T (parity A) (unif n) := by
  sorry

end GaussianSGD
