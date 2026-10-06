import GaussianSGD.Defs

/-!
# Shared elementary facts

Norms of cube points, the bound `|g| ≤ 1` on the logistic multiplier, the derivative and
continuity of `tanh`, continuity of the label-symmetric map and of its tail score,
measurability of `sgn`, history weights, the norm of the label correlation `μ`, and the second
moment of the standard Gaussian.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

lemma norm_pt_sq {n : ℕ} (x : Cube n) : ‖pt x‖ ^ 2 = n := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pt, bsign]

lemma norm_pt {n : ℕ} (x : Cube n) : ‖pt x‖ = Real.sqrt n := by
  rw [← norm_pt_sq x, Real.sqrt_sq (norm_nonneg _)]

lemma abs_g_le_one {y : ℝ} (hy : |y| ≤ 1) (z : ℝ) : |g y z| ≤ 1 := by
  unfold g
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + Real.exp (y * z)),
    div_le_one (by positivity)]
  linarith [Real.exp_pos (y * z)]

/-- The derivative of `tanh` is `sech²`. -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh ((Real.cosh x ^ 2)⁻¹) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : (Real.sinh / Real.cosh) = Real.tanh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  convert h using 1
  have := Real.cosh_sq_sub_sinh_sq x
  have hc := (Real.cosh_pos x).ne'
  field_simp
  linarith

lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_tanh x).continuousAt

lemma continuous_Rmap {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) :
    Continuous (Rmap γ ψ D) := by
  have := continuous_tanh
  unfold Rmap
  fun_prop

lemma continuous_Zsym {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ)
    (x : Cube n) : Continuous (Zsym γ ψ D T x) := by
  have := fun t : ℕ => (continuous_Rmap γ ψ D).iterate t
  unfold Zsym tailAvg
  fun_prop

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma histWeight_nonneg {n T : ℕ} (D : Dist n) (s : Fin T → Cube n) : 0 ≤ histWeight D s :=
  Finset.prod_nonneg fun i _ => D.nonneg (s i)

lemma sum_histWeight {n T : ℕ} (D : Dist n) : ∑ s : Fin T → Cube n, histWeight D s = 1 := by
  unfold histWeight
  rw [← Fintype.prod_sum (fun (_ : Fin T) x => D.p x)]
  simp [D.sum_one]

lemma err_nonneg {n : ℕ} (D : Dist n) (G : Cube n → ℝ) (h : Cube n → Bool) : 0 ≤ err D G h :=
  Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (by split_ifs <;> norm_num)

/-- The label-weighted ReLU feature average `E_D h(x) ReLU⟪w, x⟫`. -/
def corrFn {n : ℕ} (h : Cube n → Bool) (D : Dist n) (w : Vec n) : ℝ :=
  ∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫

/-- `‖μ‖² = m⁻¹ ∑_j (E_D h(x) ReLU⟪W_j, x⟫)²`. -/
lemma norm_mu_sq {n m : ℕ} (W : Fin m → Vec n) (h : Cube n → Bool) (D : Dist n) :
    ‖mu (psi W) h D‖ ^ 2 = (m : ℝ)⁻¹ * ∑ j, corrFn h D (W j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mu, psi, hid, corrFn, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  have : ∀ x, D.p x * bsign (h x) * ((Real.sqrt m)⁻¹ * relu ⟪W j, pt x⟫) =
      (Real.sqrt m)⁻¹ * (D.p x * bsign (h x) * relu ⟪W j, pt x⟫) := fun x => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

/-- `E Z² = 1` for `Z ∼ N(0,1)`. -/
lemma integral_sq_gaussianReal : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

end GaussianSGD
