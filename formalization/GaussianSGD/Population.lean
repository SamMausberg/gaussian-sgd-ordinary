import GaussianSGD.Defs

/-!
# Sampling and label effects (`lem:population`)

The logistic decomposition, nonexpansivity of the sample, population, and
label-symmetric maps, the sampling-error bound for the frozen recurrence against
its population recurrence, and the label effect.
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace GaussianSGD

/-- The logistic decomposition `y/(1+e^{yz}) = y/2 - tanh(z/2)/2` for `y = ±1`. -/
theorem g_bsign (b : Bool) (z : ℝ) : g (bsign b) z = bsign b / 2 - Real.tanh (z / 2) / 2 := by
  sorry

/-- The population map is the conditional mean of one frozen sample update. -/
theorem Pmap_eq_mean {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (h : Cube n → Bool) (D : Dist n)
    (v : Vec m) :
    Pmap γ ψ h D v = ∑ x, D.p x • (v + (γ * g (bsign (h x)) ⟪v, ψ x⟫) • ψ x) := by
  sorry

/-- `R` is odd. -/
theorem Rmap_neg {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (v : Vec m) :
    Rmap γ ψ D (-v) = -Rmap γ ψ D v := by
  sorry

/-- `R` is nonexpansive. -/
theorem Rmap_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (v w : Vec m) :
    ‖Rmap γ ψ D v - Rmap γ ψ D w‖ ≤ ‖v - w‖ := by
  sorry

/-- `P = R + γμ/2` is nonexpansive. -/
theorem Pmap_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (v w : Vec m) :
    ‖Pmap γ ψ h D v - Pmap γ ψ h D w‖ ≤ ‖v - w‖ := by
  sorry

/-- Each sample map `v ↦ v + γ g(y, ⟪v, ψ(x)⟫) ψ(x)` is nonexpansive. -/
theorem sample_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (x : Cube n) {y : ℝ}
    (hy : y = 1 ∨ y = -1) (v w : Vec m) :
    ‖(v + (γ * g y ⟪v, ψ x⟫) • ψ x) - (w + (γ * g y ⟪w, ψ x⟫) • ψ x)‖ ≤ ‖v - w‖ := by
  sorry

/-- Sampling and label effects (`lem:population`), sampling part: `E ‖u_t - v_t‖² ≤ t γ² Λ` for every initial vector,
where the expectation is over histories drawn from `D^T` and `t ≤ T`. -/
theorem frozen_sq_error {n m T : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (t : ℕ) (ht : t ≤ T) :
    ∑ s : Fin T → Cube n, histWeight D s *
        ‖frozen γ ψ (ext s) (labels h (ext s)) b0 t - (Pmap γ ψ h D)^[t] b0‖ ^ 2
      ≤ t * γ ^ 2 * (9 / 16) := by
  sorry

/-- Sampling and label effects (`lem:population`), label part: `‖v_t - z_t‖ ≤ t γ ‖μ‖ / 2`. -/
theorem label_effect {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (t : ℕ) :
    ‖(Pmap γ ψ h D)^[t] b0 - (Rmap γ ψ D)^[t] b0‖ ≤ t * γ * ‖mu ψ h D‖ / 2 := by
  sorry

/-- Sampling and label effects (`lem:population`), tail sampling part: `E ‖ū - v̄‖² ≤ Λ B² / T` with `B = γ T`. -/
theorem tail_sq_error {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) :
    ∑ s : Fin T → Cube n, histWeight D s *
        ‖tailAvg T (frozen γ ψ (ext s) (labels h (ext s)) b0) -
          tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0)‖ ^ 2
      ≤ 9 / 16 * (γ * T) ^ 2 / T := by
  sorry

/-- Sampling and label effects (`lem:population`), tail label part: `|⟪v̄ - z̄, ψ(x)⟫| ≤ 3 B ‖μ‖ / 8` with `B = γ T`. -/
theorem tail_label_effect {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (x : Cube n) :
    |⟪tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0) - tailAvg T (fun t => (Rmap γ ψ D)^[t] b0),
        ψ x⟫| ≤ 3 * (γ * T) / 8 * ‖mu ψ h D‖ := by
  sorry

end GaussianSGD
