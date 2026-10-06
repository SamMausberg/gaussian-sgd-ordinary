import GaussianSGD.Defs

/-!
# The label-symmetric map `R`

Properties of `R(v) = v - (γ/2) E_D[ψ(x) tanh(⟪v, ψ(x)⟫/2)]` used for the density at the
beginning of the tail (`lem:density`): `R` does not increase norms, it is injective, its
derivative is `I - γ H(v)` (`eq:H`), and `det DR(v) ≥ 1 - 9γ/64` when `‖ψ(x)‖² ≤ 9/16`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory

namespace GaussianSGD.DensityAux

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

lemma tanh_monotone : Monotone Real.tanh :=
  monotone_of_deriv_nonneg (fun x => (hasDerivAt_tanh x).differentiableAt)
    (fun x => by rw [(hasDerivAt_tanh x).deriv]; positivity)

lemma sub_tanh_monotone : Monotone (fun x => x - Real.tanh x) := by
  have hd : ∀ x, HasDerivAt (fun x => x - Real.tanh x) (1 - (Real.cosh x ^ 2)⁻¹) x :=
    fun x => (hasDerivAt_id x).sub (hasDerivAt_tanh x)
  refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) (fun x => ?_)
  rw [(hd x).deriv, sub_nonneg]
  have h1 : 1 ≤ Real.cosh x ^ 2 := by nlinarith [Real.one_le_cosh x]
  exact inv_le_one_of_one_le₀ h1

/-- `tanh` is nondecreasing and `1`-Lipschitz, in the form used for the map `R`. -/
lemma tanh_sub_bounds (a b : ℝ) :
    (Real.tanh a - Real.tanh b) ^ 2 ≤ (Real.tanh a - Real.tanh b) * (a - b) ∧
      (Real.tanh a - Real.tanh b) * (a - b) ≤ (a - b) ^ 2 := by
  rcases le_total b a with h | h
  · have h1 := tanh_monotone h
    have h2 := sub_tanh_monotone h
    simp only at h2
    constructor <;> nlinarith
  · have h1 := tanh_monotone h
    have h2 := sub_tanh_monotone h
    simp only at h2
    constructor <;> nlinarith

variable {n m : ℕ} {γ : ℝ} {ψ : Cube n → Vec m} {D : Dist n}

lemma norm_psi_le (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (x : Cube n) : ‖ψ x‖ ≤ 3 / 4 := by
  nlinarith [hψ x, norm_nonneg (ψ x)]

/-- The map `R` does not increase norms. Since `R 0 = 0`, this is the case `w = 0` of the
nonexpansiveness of `R`. -/
lemma norm_Rmap_le (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16)
    (v : Vec m) : ‖Rmap γ ψ D v‖ ≤ ‖v‖ := by
  set u : Cube n → ℝ := fun x => ⟪v, ψ x⟫ / 2 with hu
  set t : Cube n → ℝ := fun x => Real.tanh (u x) with ht
  set N : Vec m := (γ / 2) • ∑ x, (D.p x * t x) • ψ x with hN
  have hR : Rmap γ ψ D v = v - N := rfl
  have hinner : ⟪v, N⟫ = γ * ∑ x, D.p x * (t x * u x) := by
    rw [hN, real_inner_smul_right, inner_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [real_inner_smul_right, hu]
    ring
  have htu : ∀ x, t x ^ 2 ≤ t x * u x := fun x => by
    have := (tanh_sub_bounds (u x) 0).1
    simpa [Real.tanh_zero] using this
  set M := ∑ x, D.p x * |t x| with hM
  have hNle : ‖N‖ ≤ (γ / 2) * ((3 / 4) * M) := by
    rw [hN, norm_smul, Real.norm_of_nonneg (by linarith)]
    gcongr
    calc ‖∑ x, (D.p x * t x) • ψ x‖ ≤ ∑ x, ‖(D.p x * t x) • ψ x‖ := norm_sum_le _ _
      _ ≤ ∑ x, (3 / 4) * (D.p x * |t x|) := by
        gcongr with x
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (D.nonneg x)]
        have := norm_psi_le hψ x
        have h0 : 0 ≤ D.p x * |t x| := mul_nonneg (D.nonneg x) (abs_nonneg _)
        nlinarith
      _ = (3 / 4) * M := by rw [hM, Finset.mul_sum]
  have hM2 : M ^ 2 ≤ ∑ x, D.p x * t x ^ 2 := by
    have h0 : 0 ≤ ∑ x, D.p x * (|t x| - M) ^ 2 :=
      Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (sq_nonneg _)
    have e : ∀ x, D.p x * (|t x| - M) ^ 2
        = D.p x * t x ^ 2 - 2 * M * (D.p x * |t x|) + M ^ 2 * D.p x := by
      intro x; rw [sub_sq, sq_abs]; ring
    simp_rw [e] at h0
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      D.sum_one, ← hM] at h0
    nlinarith
  have hS : ∑ x, D.p x * t x ^ 2 ≤ ∑ x, D.p x * (t x * u x) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (htu x) (D.nonneg x)
  have hS0 : 0 ≤ ∑ x, D.p x * t x ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (sq_nonneg _)
  have hN2 : ‖N‖ ^ 2 ≤ 2 * (γ * ∑ x, D.p x * (t x * u x)) := by
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (abs_nonneg _)
    calc ‖N‖ ^ 2 ≤ ((γ / 2) * ((3 / 4) * M)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNle 2
      _ = (9 * γ ^ 2 / 64) * M ^ 2 := by ring
      _ ≤ (9 * γ ^ 2 / 64) * ∑ x, D.p x * (t x * u x) := by gcongr; linarith
      _ ≤ 2 * (γ * ∑ x, D.p x * (t x * u x)) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (hS0.trans hS)
        nlinarith
  have hsq : ‖Rmap γ ψ D v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hR, norm_sub_sq_real, hinner]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Strong monotonicity of `R`: `⟪R v - R w, v - w⟫ ≥ (1 - 9γ/64) ‖v - w‖²`, where
`9γ/64 = γΛ/4` with `Λ = 9/16`. -/
lemma inner_Rmap_sub_ge (hγ0 : 0 ≤ γ) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (v w : Vec m) :
    (1 - 9 * γ / 64) * ‖v - w‖ ^ 2 ≤ ⟪Rmap γ ψ D v - Rmap γ ψ D w, v - w⟫ := by
  set e : Cube n → ℝ := fun x => ⟪v, ψ x⟫ / 2 - ⟪w, ψ x⟫ / 2 with he
  set d : Cube n → ℝ := fun x => Real.tanh (⟪v, ψ x⟫ / 2) - Real.tanh (⟪w, ψ x⟫ / 2) with hd
  have key : ⟪Rmap γ ψ D v - Rmap γ ψ D w, v - w⟫
      = ‖v - w‖ ^ 2 - (γ / 2) * ∑ x, D.p x * (d x * (2 * e x)) := by
    have hdiff : Rmap γ ψ D v - Rmap γ ψ D w
        = (v - w) - (γ / 2) • ∑ x, (D.p x * d x) • ψ x := by
      simp only [Rmap, hd, mul_sub, sub_smul, Finset.sum_sub_distrib, smul_sub]
      abel
    rw [hdiff, inner_sub_left, real_inner_self_eq_norm_sq, real_inner_smul_left, sum_inner]
    congr 2
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [real_inner_smul_left, inner_sub_right, real_inner_comm v (ψ x),
      real_inner_comm w (ψ x)]
    simp only [he]
    ring
  have hterm : ∀ x, D.p x * (d x * (2 * e x)) ≤ D.p x * (9 / 32 * ‖v - w‖ ^ 2) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (D.nonneg x)
    have h1 := (tanh_sub_bounds (⟪v, ψ x⟫ / 2) (⟪w, ψ x⟫ / 2)).2
    have h2 : e x = ⟪v - w, ψ x⟫ / 2 := by rw [he, inner_sub_left]; ring
    have h3 : ⟪v - w, ψ x⟫ ^ 2 ≤ ‖v - w‖ ^ 2 * (9 / 16) := by
      have := abs_real_inner_le_norm (v - w) (ψ x)
      have h4 : ⟪v - w, ψ x⟫ ^ 2 ≤ (‖v - w‖ * ‖ψ x‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      rw [mul_pow] at h4
      nlinarith [hψ x, sq_nonneg ‖v - w‖]
    have : d x * (2 * e x) ≤ 2 * e x ^ 2 := by
      have : d x * e x ≤ e x ^ 2 := h1
      linarith
    rw [h2] at this ⊢
    nlinarith
  have hsum : ∑ x, D.p x * (d x * (2 * e x)) ≤ 9 / 32 * ‖v - w‖ ^ 2 := by
    calc ∑ x, D.p x * (d x * (2 * e x)) ≤ ∑ x, D.p x * (9 / 32 * ‖v - w‖ ^ 2) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = 9 / 32 * ‖v - w‖ ^ 2 := by rw [← Finset.sum_mul, D.sum_one, one_mul]
  rw [key]
  nlinarith

lemma Rmap_injective (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) :
    Function.Injective (Rmap γ ψ D) := by
  intro v w h
  have := inner_Rmap_sub_ge (D := D) hγ0 hψ v w
  rw [h, sub_self, inner_zero_left] at this
  have hpos : 0 < 1 - 9 * γ / 64 := by linarith
  have : ‖v - w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v - w‖]
  have : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- The operator `γ H(v)`, where `H(v) = (1/4) E_D[ψ(x) ψ(x)ᵀ sech²(⟪v, ψ(x)⟫/2)]` as in
`eq:H`. -/
def gammaH (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (v : Vec m) : Vec m →L[ℝ] Vec m :=
  ∑ x, (γ / 4 * D.p x * (Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹) • (innerSL ℝ (ψ x)).smulRight (ψ x)

lemma gammaH_apply (v δ : Vec m) :
    gammaH γ ψ D v δ
      = ∑ x, (γ / 4 * D.p x * (Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹ * ⟪ψ x, δ⟫) • ψ x := by
  simp [gammaH, smul_smul]

/-- The derivative of `R` is `DR(v) = I - γ H(v)` (`eq:H`). -/
lemma hasFDerivAt_Rmap (v : Vec m) :
    HasFDerivAt (Rmap γ ψ D) (ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D v) v := by
  have hx : ∀ x ∈ (Finset.univ : Finset (Cube n)),
      HasFDerivAt (fun w : Vec m => (D.p x * Real.tanh (⟪w, ψ x⟫ / 2)) • ψ x)
        (((D.p x * ((Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹ * (1 / 2))) •
          innerSL ℝ (ψ x)).smulRight (ψ x)) v := by
    intro x _
    have hin : HasFDerivAt (fun w : Vec m => ⟪w, ψ x⟫) (innerSL ℝ (ψ x)) v := by
      have := (innerSL ℝ (ψ x)).hasFDerivAt (x := v)
      convert this using 1
      funext w
      simp [real_inner_comm]
    have hs : HasDerivAt (fun y : ℝ => D.p x * Real.tanh (y / 2))
        (D.p x * ((Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹ * (1 / 2))) ⟪v, ψ x⟫ := by
      have h1 := (hasDerivAt_tanh (⟪v, ψ x⟫ / 2)).comp ⟪v, ψ x⟫
        ((hasDerivAt_id ⟪v, ψ x⟫).div_const 2)
      exact h1.const_mul (D.p x)
    exact (hs.comp_hasFDerivAt v hin).smul_const (ψ x)
  have h := (hasFDerivAt_id v).sub ((HasFDerivAt.sum hx).const_smul (γ / 2))
  have hfun : Rmap γ ψ D
      = (id - (γ / 2) • ∑ x, fun w : Vec m => (D.p x * Real.tanh (⟪w, ψ x⟫ / 2)) • ψ x) := by
    funext w
    simp [Rmap, Finset.sum_apply]
  rw [hfun]
  refine h.congr_fderiv ?_
  ext δ i
  simp [gammaH_apply, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma differentiable_Rmap : Differentiable ℝ (Rmap γ ψ D) :=
  fun v => (hasFDerivAt_Rmap v).differentiableAt

/-- `∏ (1 - κᵢ) ≥ 1 - ∑ κᵢ` when every `κᵢ ∈ [0, 1]`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (κ : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ κ i) (h1 : ∀ i ∈ s, κ i ≤ 1) :
    1 - ∑ i ∈ s, κ i ≤ ∏ i ∈ s, (1 - κ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hj0 := h0 j (Finset.mem_insert_self j s)
    have hj1 := h1 j (Finset.mem_insert_self j s)
    have hs0 : 0 ≤ ∑ i ∈ s, κ i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    nlinarith

/-- Determinant bound: `det DR(v) ≥ 1 - γ tr H(v) ≥ 1 - 9γ/64`. The first inequality applies
`∏ (1 - κᵢ) ≥ 1 - ∑ κᵢ` to the eigenvalues `κᵢ ∈ [0, 1]` of `γ H(v)`. -/
lemma det_DR_ge (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (v : Vec m) :
    1 - 9 * γ / 64 ≤ (ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D v).det := by
  set c : Cube n → ℝ := fun x => γ / 4 * D.p x * (Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹ with hc
  have hc0 : ∀ x, 0 ≤ c x := fun x => by
    have := D.nonneg x
    simp only [hc]; positivity
  have hc1 : ∀ x, c x ≤ γ / 4 * D.p x := fun x => by
    have h1 : 1 ≤ Real.cosh (⟪v, ψ x⟫ / 2) ^ 2 := by
      nlinarith [Real.one_le_cosh (⟪v, ψ x⟫ / 2)]
    have h2 : (Real.cosh (⟪v, ψ x⟫ / 2) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h3 : 0 ≤ γ / 4 * D.p x := mul_nonneg (by linarith) (D.nonneg x)
    simp only [hc]
    nlinarith
  set T : Vec m →ₗ[ℝ] Vec m :=
    ((ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D v : Vec m →L[ℝ] Vec m) :
      Vec m →ₗ[ℝ] Vec m) with hTdef
  have hTinner : ∀ δ ε : Vec m, ⟪T δ, ε⟫ = ⟪δ, ε⟫ - ∑ x, c x * (⟪ψ x, δ⟫ * ⟪ψ x, ε⟫) := by
    intro δ ε
    simp only [hTdef, ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id,
      LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, gammaH_apply,
      inner_sub_left, sum_inner, real_inner_smul_left, hc]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [real_inner_comm ε (ψ x)]
    ring
  have hT : T.IsSymmetric := by
    intro δ ε
    rw [hTinner, real_inner_comm (T ε) δ, hTinner, real_inner_comm δ ε]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  have hn : Module.finrank ℝ (Vec m) = m := finrank_euclideanSpace_fin
  set b := hT.eigenvectorBasis hn with hb
  set κ : Fin m → ℝ := fun i => ∑ x, c x * ⟪ψ x, b i⟫ ^ 2 with hκ
  have hμ : ∀ i, hT.eigenvalues hn i = 1 - κ i := by
    intro i
    have h1 : ⟪T (b i), b i⟫ = hT.eigenvalues hn i := by
      rw [hb, hT.apply_eigenvectorBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
        OrthonormalBasis.norm_eq_one]
      simp
    rw [← h1, hTinner, real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one]
    simp [hκ, sq]
  have hκ0 : ∀ i, 0 ≤ κ i := fun i =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hc0 x) (sq_nonneg _)
  have hκsum : ∑ i, κ i ≤ 9 * γ / 64 := by
    calc ∑ i, κ i = ∑ x, c x * ‖ψ x‖ ^ 2 := by
          simp only [hκ]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, b.sum_sq_inner_left]
      _ ≤ ∑ x, (γ / 4 * D.p x) * (9 / 16) := by
          exact Finset.sum_le_sum fun x _ =>
            mul_le_mul (hc1 x) (hψ x) (sq_nonneg _) (mul_nonneg (by linarith) (D.nonneg x))
      _ = 9 * γ / 64 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, D.sum_one]
          ring
  have hκ1 : ∀ i, κ i ≤ 1 := fun i => by
    have : κ i ≤ ∑ j, κ j :=
      Finset.single_le_sum (fun j _ => hκ0 j) (Finset.mem_univ i)
    linarith
  have hdet : (ContinuousLinearMap.id ℝ (Vec m) - gammaH γ ψ D v).det = ∏ i, (1 - κ i) := by
    change LinearMap.det T = _
    rw [hT.det_eq_prod_eigenvalues hn]
    simp [hμ]
  rw [hdet]
  exact le_trans (by linarith)
    (one_sub_sum_le_prod_one_sub Finset.univ κ (fun i _ => hκ0 i) (fun i _ => hκ1 i))

end GaussianSGD.DensityAux
