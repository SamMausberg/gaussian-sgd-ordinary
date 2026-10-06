import GaussianSGD.Defs

/-!
# The standard Gaussian density on `Vec m`

The standard Gaussian measure on `ℝ^m` is Lebesgue measure with density
`(2π)^{-m/2} exp(-‖v‖²/2)`. The identification goes through characteristic functions.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD.DensityAux

/-- The normalizing constant `(2π)^{m/2}`. -/
def gaussZ (m : ℕ) : ℝ := (2 * Real.pi) ^ ((m : ℝ) / 2)

lemma integral_gauss (m : ℕ) :
    ∫ v : Vec m, Real.exp (-(1 / 2) * ‖v‖ ^ 2) = gaussZ m := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Vec m) (b := 1 / 2) (by norm_num)
  rw [this, finrank_euclideanSpace_fin, gaussZ]
  congr 1
  ring

lemma gaussZ_pos (m : ℕ) : 0 < gaussZ m := by
  unfold gaussZ; positivity

/-- The standard Gaussian density `(2π)^{-m/2} exp(-‖v‖²/2)`. -/
def gaussDens (m : ℕ) (v : Vec m) : ℝ := Real.exp (-(1 / 2) * ‖v‖ ^ 2) / gaussZ m

/-- The Gaussian density is a nonincreasing function of the norm. -/
lemma gaussDens_le_of_norm_le {m : ℕ} {v w : Vec m} (h : ‖w‖ ≤ ‖v‖) :
    gaussDens m v ≤ gaussDens m w := by
  unfold gaussDens
  apply div_le_div_of_nonneg_right _ (gaussZ_pos m).le
  apply Real.exp_le_exp.2
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2]

/-- The standard Gaussian measure on `Vec m` is Lebesgue measure with density `gaussDens m`. -/
lemma stdGaussian_eq_withDensity (m : ℕ) :
    stdGaussian (Vec m) = volume.withDensity (fun v => ENNReal.ofReal (gaussDens m v)) := by
  have hZ := gaussZ_pos m
  have hint : Integrable (fun v : Vec m => gaussDens m v) := by
    refine Integrable.div_const (Integrable.of_integral_ne_zero ?_) _
    rw [integral_gauss]; exact hZ.ne'
  have : IsProbabilityMeasure
      ((volume : Measure (Vec m)).withDensity (fun v => ENNReal.ofReal (gaussDens m v))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun v => by unfold gaussDens; positivity)]
    unfold gaussDens
    rw [integral_div, integral_gauss, div_self hZ.ne', ENNReal.ofReal_one]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul
      (Measurable.ennreal_ofReal (by unfold gaussDens; fun_prop))
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∀ x : Vec m,
      (ENNReal.ofReal (gaussDens m x)).toReal • Complex.exp (⟪x, t⟫ * Complex.I)
        = ((gaussZ m : ℂ))⁻¹ *
          Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * ⟪t, x⟫) := by
    intro x
    rw [ENNReal.toReal_ofReal (by unfold gaussDens; positivity), Complex.real_smul, gaussDens,
      Complex.ofReal_div, Complex.ofReal_exp, div_eq_inv_mul, mul_assoc, ← Complex.exp_add,
      real_inner_comm]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num),
    finrank_euclideanSpace_fin, gaussZ, Complex.ofReal_cpow (by positivity)]
  have e2 : (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [e2]
  have hne : (((2 * Real.pi : ℝ) : ℂ)) ^ (((m : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [Real.pi_ne_zero]
  push_cast at hne ⊢
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  congr 1
  simp only [Complex.I_sq]
  ring

end GaussianSGD.DensityAux
