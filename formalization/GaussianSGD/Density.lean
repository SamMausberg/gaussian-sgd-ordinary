import GaussianSGD.Defs
import GaussianSGD.DensityGaussian
import GaussianSGD.DensityMap

/-!
# Density at the beginning of the tail (`lem:density`)

Started from a standard Gaussian vector, the label-symmetric recurrence at time
`s = ⌈T/2⌉` has law at most `e` times the standard Gaussian law. Equivalently, its
density is at most `e (2π)^{-m/2} exp(-‖v‖²/2)`.

The proof bounds a single step. For a measurable set `A` and `S = R⁻¹(A)`, change of
variables on `S`, with `det DR ≥ 1 - 9γ/64` and `‖R v‖ ≤ ‖v‖`, gives
`γ_m(R⁻¹(A)) ≤ (1 - 9γ/64)⁻¹ γ_m(A)`. Only injectivity of `R` is needed.
Iterating `s` times and using `s · 9γ/64 ≤ 1 - 9γ/64` gives the factor `e`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace DensityAux

variable {n m : ℕ} {γ : ℝ} {ψ : Cube n → Vec m} {D : Dist n}

lemma measurable_Rmap : Measurable (Rmap γ ψ D) :=
  differentiable_Rmap.continuous.measurable

/-- One step of `R` multiplies the standard Gaussian law by at most `(1 - 9γ/64)⁻¹`. -/
lemma map_Rmap_le (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) :
    (stdGaussian (Vec m)).map (Rmap γ ψ D)
      ≤ ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) • stdGaussian (Vec m) := by
  have hpos : 0 < 1 - 9 * γ / 64 := by linarith
  set c := ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) with hc
  set ρ : Vec m → ENNReal := fun v => ENNReal.ofReal (gaussDens m v) with hρ
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply measurable_Rmap hA, Measure.smul_apply, smul_eq_mul]
  set S := Rmap γ ψ D ⁻¹' A with hSdef
  have hS : MeasurableSet S := measurable_Rmap hA
  rw [stdGaussian_eq_withDensity, withDensity_apply' _ S, withDensity_apply' _ A]
  have hCoV := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x _ => (hasFDerivAt_Rmap (γ := γ) (ψ := ψ) (D := D) x).hasFDerivWithinAt)
    ((Rmap_injective (D := D) hγ0 hγ hψ).injOn) ρ
  have hpt : ∀ x, ρ x ≤ c * (ENNReal.ofReal
      |(ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D x).det| * ρ (Rmap γ ψ D x)) := by
    intro x
    have hone : 1 ≤ c * ENNReal.ofReal
        |(ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D x).det| := by
      rw [hc, ← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, one_le_div hpos]
      exact (det_DR_ge hγ0 hγ hψ x).trans (le_abs_self _)
    calc ρ x ≤ ρ (Rmap γ ψ D x) :=
          ENNReal.ofReal_le_ofReal (gaussDens_le_of_norm_le (norm_Rmap_le hγ0 hγ hψ x))
      _ = 1 * ρ (Rmap γ ψ D x) := (one_mul _).symm
      _ ≤ _ := by rw [← mul_assoc]; gcongr
  calc ∫⁻ x in S, ρ x
      ≤ ∫⁻ x in S, c * (ENNReal.ofReal
          |(ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D x).det| * ρ (Rmap γ ψ D x)) :=
        lintegral_mono fun x => hpt x
    _ = c * ∫⁻ x in Rmap γ ψ D '' S, ρ x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCoV]
    _ ≤ c * ∫⁻ x in A, ρ x := by
        gcongr
        exact Set.image_preimage_subset _ _

/-- After `k` steps the factor is `(1 - 9γ/64)^{-k}`. -/
lemma map_Rmap_iterate_le (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16)
    (k : ℕ) :
    (stdGaussian (Vec m)).map ((Rmap γ ψ D)^[k])
      ≤ ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) ^ k • stdGaussian (Vec m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', ← Measure.map_map measurable_Rmap (measurable_Rmap.iterate k)]
    calc ((stdGaussian (Vec m)).map ((Rmap γ ψ D)^[k])).map (Rmap γ ψ D)
        ≤ (ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) ^ k • stdGaussian (Vec m)).map (Rmap γ ψ D) :=
          Measure.map_mono ih measurable_Rmap
      _ = ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) ^ k •
            (stdGaussian (Vec m)).map (Rmap γ ψ D) :=
          Measure.map_smul _ measurable_Rmap.aemeasurable
      _ ≤ ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) ^ k •
            (ENNReal.ofReal ((1 - 9 * γ / 64)⁻¹) • stdGaussian (Vec m)) := by
          rw [Measure.le_iff]
          intro A hA
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
          exact Measure.le_iff.1 (map_Rmap_le hγ0 hγ hψ) A hA
      _ = _ := by rw [smul_smul, pow_succ]

end DensityAux

open DensityAux

/-- Density at the beginning of the tail (`lem:density`). -/
theorem density_bound {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) :
    (stdGaussian (Vec m)).map ((Rmap γ ψ D)^[(T + 1) / 2])
      ≤ ENNReal.ofReal (Real.exp 1) • stdGaussian (Vec m) := by
  -- The bound holds for every `T`; the hypothesis `1 ≤ T` is not needed.
  have _ := hT
  set s := (T + 1) / 2 with hsdef
  set a := 9 * γ / 64 with ha
  have hpos : 0 < 1 - a := by linarith
  have hs : (s : ℝ) ≤ ((T : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := T + 1) (n := 2)
    push_cast at this
    exact this
  have key : (s : ℝ) * a ≤ 1 - a := by
    have := mul_le_mul_of_nonneg_left hs hγ0.le
    nlinarith
  have h1 : (1 - a)⁻¹ ≤ Real.exp (a / (1 - a)) := by
    have h := Real.add_one_le_exp (a / (1 - a))
    have e : a / (1 - a) + 1 = (1 - a)⁻¹ := by field_simp; ring
    rw [e] at h
    exact h
  have h2 : ((1 - a)⁻¹) ^ s ≤ Real.exp 1 := by
    calc ((1 - a)⁻¹) ^ s ≤ (Real.exp (a / (1 - a))) ^ s :=
          pow_le_pow_left₀ (inv_nonneg.2 hpos.le) h1 s
      _ = Real.exp (s * (a / (1 - a))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := by
          apply Real.exp_le_exp.2
          rw [← mul_div_assoc, div_le_one hpos]
          exact key
  refine (map_Rmap_iterate_le hγ0.le hγ hψ s).trans ?_
  rw [Measure.le_iff]
  intro A _
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  rw [← ENNReal.ofReal_pow (inv_nonneg.2 hpos.le)]
  exact ENNReal.ofReal_le_ofReal h2

end GaussianSGD
