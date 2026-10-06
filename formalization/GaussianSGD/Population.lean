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

namespace Population

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have he : Real.sinh / Real.cosh = Real.tanh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [he] at h
  convert h using 1
  have := Real.cosh_sq_sub_sinh_sq x
  have hc := (Real.cosh_pos x).ne'
  field_simp
  linarith

theorem continuous_tanh : Continuous Real.tanh := by
  have he : (fun y => Real.sinh y / Real.cosh y) = Real.tanh := by
    funext y; rw [Real.tanh_eq_sinh_div_cosh]
  rw [← he]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun y => (Real.cosh_pos y).ne')

/-- A secant slope of `tanh` lies in `[0, 1]`. -/
theorem tanh_secant (p q : ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ 1 ∧ Real.tanh p - Real.tanh q = κ * (p - q) := by
  have key : ∀ a b : ℝ, a < b →
      ∃ κ : ℝ, 0 ≤ κ ∧ κ ≤ 1 ∧ Real.tanh b - Real.tanh a = κ * (b - a) := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope Real.tanh (fun y => 1 / Real.cosh y ^ 2) hab
      continuous_tanh.continuousOn (fun y _ => hasDerivAt_tanh y)
    refine ⟨1 / Real.cosh c ^ 2, by positivity, ?_, ?_⟩
    · have h1 := Real.one_le_cosh c
      rw [div_le_one (by positivity)]
      nlinarith
    · rw [hc]
      field_simp [(sub_pos.mpr hab).ne']
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · obtain ⟨κ, h0, h1, he⟩ := key p q hpq
    exact ⟨κ, h0, h1, by linarith⟩
  · exact ⟨0, le_rfl, zero_le_one, by simp [hpq]⟩
  · exact key q p hpq

end Population

open Population

/-- The logistic decomposition `y/(1+e^{yz}) = y/2 - tanh(z/2)/2` for `y = ±1`. -/
theorem g_bsign (b : Bool) (z : ℝ) : g (bsign b) z = bsign b / 2 - Real.tanh (z / 2) / 2 := by
  have ha := Real.exp_pos (z / 2)
  have hz : Real.exp z = Real.exp (z / 2) * Real.exp (z / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hnz : Real.exp (-z) = (Real.exp (z / 2))⁻¹ * (Real.exp (z / 2))⁻¹ := by
    rw [Real.exp_neg, hz, mul_inv]
  have ht : Real.tanh (z / 2) = (Real.exp (z / 2) - (Real.exp (z / 2))⁻¹) /
      (Real.exp (z / 2) + (Real.exp (z / 2))⁻¹) := by
    rw [Real.tanh_eq, Real.exp_neg]
  cases b
  · simp only [g, bsign, Bool.false_eq_true, ite_false, neg_one_mul]
    rw [hnz, ht]
    field_simp
    ring
  · simp only [g, bsign, ite_true, one_mul]
    rw [hz, ht]
    field_simp
    ring

/-- The population map is the conditional mean of one frozen sample update. -/
theorem Pmap_eq_mean {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (h : Cube n → Bool) (D : Dist n)
    (v : Vec m) :
    Pmap γ ψ h D v = ∑ x, D.p x • (v + (γ * g (bsign (h x)) ⟪v, ψ x⟫) • ψ x) := by
  simp only [smul_add, sum_add_distrib, ← sum_smul, D.sum_one, one_smul, Pmap, Rmap, mu,
    smul_sum, smul_smul, g_bsign]
  rw [sub_add_eq_add_sub, add_sub_assoc, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← sub_smul]
  congr 1
  ring

/-- `R` is odd. -/
theorem Rmap_neg {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (v : Vec m) :
    Rmap γ ψ D (-v) = -Rmap γ ψ D v := by
  simp only [Rmap, inner_neg_left, neg_div, Real.tanh_neg, mul_neg, neg_smul, sum_neg_distrib,
    smul_neg]
  abel

namespace Population

/-- A perturbation `δ - γ K` of `δ` with `⟪δ, K⟫ = S ≥ 0` and `‖K‖² ≤ M S` is no longer than `δ`
when `γ M ≤ 2`. -/
theorem norm_sub_smul_le {m : ℕ} {δ K : Vec m} {S M γ : ℝ} (hS : ⟪δ, K⟫ = S) (hS0 : 0 ≤ S)
    (hK : ‖K‖ ^ 2 ≤ M * S) (hγ : 0 ≤ γ) (hγM : γ * M ≤ 2) : ‖δ - γ • K‖ ≤ ‖δ‖ := by
  have h2 : ‖δ - γ • K‖ ^ 2 ≤ ‖δ‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hS]
    have h1 : γ ^ 2 * ‖K‖ ^ 2 ≤ γ ^ 2 * (M * S) := mul_le_mul_of_nonneg_left hK (sq_nonneg γ)
    have h3 : γ ^ 2 * (M * S) ≤ 2 * (γ * S) := by
      have : γ * (γ * M) * S ≤ γ * 2 * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγM hγ) hS0
      nlinarith
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Weighted Cauchy-Schwarz for a sum of rank-one terms. -/
theorem norm_sum_sq_le {m : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ψ : ι → Vec m) (δ : Vec m) :
    ‖∑ i, (a i * ⟪δ, ψ i⟫) • ψ i‖ ^ 2 ≤ (∑ i, a i * ‖ψ i‖ ^ 2) * ∑ i, a i * ⟪δ, ψ i⟫ ^ 2 := by
  have h1 : ‖∑ i, (a i * ⟪δ, ψ i⟫) • ψ i‖ ≤ ∑ i, a i * |⟪δ, ψ i⟫| * ‖ψ i‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha i)]
  have h2 : (∑ i, a i * |⟪δ, ψ i⟫| * ‖ψ i‖) ^ 2 ≤
      (∑ i, a i * ‖ψ i‖ ^ 2) * ∑ i, a i * ⟪δ, ψ i⟫ ^ 2 := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => by have := ha i; positivity)
      (fun i _ => by have := ha i; positivity) (fun i _ => le_of_eq ?_)
    rw [← sq_abs ⟪δ, ψ i⟫]
    ring
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem inner_sum_eq {m : ℕ} {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → Vec m) (δ : Vec m) :
    ⟪δ, ∑ i, (a i * ⟪δ, ψ i⟫) • ψ i⟫ = ∑ i, a i * ⟪δ, ψ i⟫ ^ 2 := by
  rw [inner_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [inner_smul_right]
  ring

/-- Secant form of `DR = I - γ H`: the difference `R(v) - R(w)` is `(I - γ K)(v - w)` for a
nonnegative combination `K` of the rank-one maps `ψ(x) ψ(x)ᵀ` with weights at most `D(x)/4`. -/
theorem Rmap_sub_eq {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (v w : Vec m) :
    ∃ a : Cube n → ℝ, (∀ x, 0 ≤ a x ∧ a x ≤ D.p x / 4) ∧
      Rmap γ ψ D v - Rmap γ ψ D w = (v - w) - γ • ∑ x, (a x * ⟪v - w, ψ x⟫) • ψ x := by
  choose κ hκ0 hκ1 hκ using fun x => tanh_secant (⟪v, ψ x⟫ / 2) (⟪w, ψ x⟫ / 2)
  refine ⟨fun x => D.p x * κ x / 4, fun x => ⟨by have := D.nonneg x; have := hκ0 x; positivity,
    by have := D.nonneg x; have := hκ1 x; nlinarith⟩, ?_⟩
  simp only [Rmap]
  rw [sub_sub_sub_comm, ← smul_sub, ← sum_sub_distrib, smul_sum, smul_sum]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [← sub_smul, smul_smul, smul_smul, inner_sub_left]
  congr 1
  rw [← mul_sub, hκ x]
  ring

theorem weight_sum_le {n m : ℕ} (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16)
    (D : Dist n) (a : Cube n → ℝ) (ha : ∀ x, 0 ≤ a x ∧ a x ≤ D.p x / 4) :
    ∑ x, a x * ‖ψ x‖ ^ 2 ≤ 9 / 64 := by
  calc ∑ x, a x * ‖ψ x‖ ^ 2 ≤ ∑ x, D.p x / 4 * (9 / 16) :=
        sum_le_sum fun x _ => mul_le_mul (ha x).2 (hψ x) (sq_nonneg _)
          (by have := D.nonneg x; positivity)
    _ = 9 / 64 := by rw [← sum_mul, ← sum_div, D.sum_one]; norm_num

/-- The deviation of `R` from the identity is `(9γ/64)`-Lipschitz. -/
theorem Rmap_sub_sub_le {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (ψ : Cube n → Vec m)
    (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (v w : Vec m) :
    ‖(Rmap γ ψ D v - Rmap γ ψ D w) - (v - w)‖ ≤ 9 * γ / 64 * ‖v - w‖ := by
  obtain ⟨a, ha, he⟩ := Rmap_sub_eq γ ψ D v w
  rw [he, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hγ0]
  suffices hK' : ‖∑ x, (a x * ⟪v - w, ψ x⟫) • ψ x‖ ≤ 9 / 64 * ‖v - w‖ by
    calc γ * ‖∑ x, (a x * ⟪v - w, ψ x⟫) • ψ x‖ ≤ γ * (9 / 64 * ‖v - w‖) :=
          mul_le_mul_of_nonneg_left hK' hγ0
      _ = 9 * γ / 64 * ‖v - w‖ := by ring
  have hM := weight_sum_le ψ hψ D a ha
  have hS : ∑ x, a x * ⟪v - w, ψ x⟫ ^ 2 ≤ 9 / 64 * ‖v - w‖ ^ 2 := by
    calc ∑ x, a x * ⟪v - w, ψ x⟫ ^ 2 ≤ ∑ x, a x * ‖ψ x‖ ^ 2 * ‖v - w‖ ^ 2 := by
          refine sum_le_sum fun x _ => ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (ha x).1
          rw [← mul_pow, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            ((abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)) 2
      _ ≤ 9 / 64 * ‖v - w‖ ^ 2 := by
          rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  have hK := norm_sum_sq_le a (fun x => (ha x).1) ψ (v - w)
  have hSn : 0 ≤ ∑ x, a x * ⟪v - w, ψ x⟫ ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (ha x).1 (sq_nonneg _)
  have h2 : ‖∑ x, (a x * ⟪v - w, ψ x⟫) • ψ x‖ ^ 2 ≤ (9 / 64 * ‖v - w‖) ^ 2 := by
    calc _ ≤ (∑ x, a x * ‖ψ x‖ ^ 2) * ∑ x, a x * ⟪v - w, ψ x⟫ ^ 2 := hK
      _ ≤ 9 / 64 * (9 / 64 * ‖v - w‖ ^ 2) :=
          mul_le_mul hM hS hSn (by norm_num)
      _ = (9 / 64 * ‖v - w‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

end Population

/-- `R` is nonexpansive. -/
theorem Rmap_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (v w : Vec m) :
    ‖Rmap γ ψ D v - Rmap γ ψ D w‖ ≤ ‖v - w‖ := by
  obtain ⟨a, ha, he⟩ := Rmap_sub_eq γ ψ D v w
  rw [he]
  have hM := weight_sum_le ψ hψ D a ha
  have hSn : 0 ≤ ∑ x, a x * ⟪v - w, ψ x⟫ ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (ha x).1 (sq_nonneg _)
  refine norm_sub_smul_le (inner_sum_eq a ψ (v - w)) hSn ?_ hγ0 (M := 9 / 64) (by linarith)
  exact (norm_sum_sq_le a (fun x => (ha x).1) ψ (v - w)).trans
    (mul_le_mul_of_nonneg_right hM hSn)

/-- `P = R + γμ/2` is nonexpansive. -/
theorem Pmap_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (v w : Vec m) :
    ‖Pmap γ ψ h D v - Pmap γ ψ h D w‖ ≤ ‖v - w‖ := by
  simp only [Pmap, add_sub_add_right_eq_sub]
  exact Rmap_nonexpansive hγ0 hγ ψ hψ D v w

/-- Each sample map `v ↦ v + γ g(y, ⟪v, ψ(x)⟫) ψ(x)` is nonexpansive. -/
theorem sample_nonexpansive {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (x : Cube n) {y : ℝ}
    (hy : y = 1 ∨ y = -1) (v w : Vec m) :
    ‖(v + (γ * g y ⟪v, ψ x⟫) • ψ x) - (w + (γ * g y ⟪w, ψ x⟫) • ψ x)‖ ≤ ‖v - w‖ := by
  obtain ⟨b, rfl⟩ : ∃ b, y = bsign b := by
    rcases hy with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  obtain ⟨κ, hκ0, hκ1, hκ⟩ := tanh_secant (⟪v, ψ x⟫ / 2) (⟪w, ψ x⟫ / 2)
  have he : (v + (γ * g (bsign b) ⟪v, ψ x⟫) • ψ x) - (w + (γ * g (bsign b) ⟪w, ψ x⟫) • ψ x) =
      (v - w) - γ • ((κ / 4 * ⟪v - w, ψ x⟫) • ψ x) := by
    rw [add_sub_add_comm, ← sub_smul, smul_smul, sub_eq_add_neg (v - w), ← neg_smul]
    congr 2
    rw [g_bsign, g_bsign, inner_sub_left]
    linear_combination (-γ / 2) * hκ
  rw [he]
  have hS0 : 0 ≤ κ / 4 * ⟪v - w, ψ x⟫ ^ 2 := by positivity
  refine norm_sub_smul_le (S := κ / 4 * ⟪v - w, ψ x⟫ ^ 2) (M := 9 / 64) ?_ hS0 ?_ hγ0
    (by linarith)
  · rw [inner_smul_right]; ring
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have : κ / 4 * ‖ψ x‖ ^ 2 ≤ 9 / 64 := by
      have := hψ x; have := norm_nonneg (ψ x); nlinarith
    calc (κ / 4 * ⟪v - w, ψ x⟫) ^ 2 * ‖ψ x‖ ^ 2
        = (κ / 4 * ‖ψ x‖ ^ 2) * (κ / 4 * ⟪v - w, ψ x⟫ ^ 2) := by ring
      _ ≤ 9 / 64 * (κ / 4 * ⟪v - w, ψ x⟫ ^ 2) := mul_le_mul_of_nonneg_right this hS0


namespace Population

theorem frozen_congr {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (b0 : Vec m) {xs xs' : ℕ → Cube n}
    {ys ys' : ℕ → ℝ} (t : ℕ) (hx : ∀ k < t, xs k = xs' k) (hy : ∀ k < t, ys k = ys' k) :
    frozen γ ψ xs ys b0 t = frozen γ ψ xs' ys' b0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [frozen]
    rw [ih (fun k hk => hx k (by omega)) (fun k hk => hy k (by omega)), hx t (by omega),
      hy t (by omega)]

theorem histWeight_nonneg {n T : ℕ} (D : Dist n) (s : Fin T → Cube n) : 0 ≤ histWeight D s :=
  prod_nonneg fun i _ => D.nonneg (s i)

theorem sum_histWeight {n T : ℕ} (D : Dist n) : ∑ s : Fin T → Cube n, histWeight D s = 1 := by
  simp only [histWeight]
  rw [← Fintype.prod_sum (fun (_ : Fin T) x => D.p x)]
  simp [D.sum_one]

/-- Integrating out one coordinate of a history drawn from `D^T`. -/
theorem sum_histWeight_update {n T : ℕ} (D : Dist n) (i : Fin T)
    (F : (Fin T → Cube n) → ℝ) :
    ∑ s, histWeight D s * F s =
      ∑ s, histWeight D s * ∑ x, D.p x * F (Function.update s i x) := by
  let e := Equiv.funSplitAt i (Cube n)
  have hw : ∀ x r, histWeight D (e.symm (x, r)) = D.p x * ∏ j, D.p (r j) := by
    intro x r
    rw [histWeight, Fintype.prod_eq_mul_prod_subtype_ne _ i]
    congr 1
    · simp [e]
    · refine Fintype.prod_congr _ _ fun j => ?_
      simp [e, j.2]
  have hu : ∀ x' r x, Function.update (e.symm (x', r)) i x = e.symm (x, r) := by
    intro x' r x
    funext j
    by_cases hj : j = i
    · subst hj; simp [e]
    · simp [e, hj]
  rw [← e.symm.sum_comp (fun s => histWeight D s * F s),
    ← e.symm.sum_comp (fun s => histWeight D s * ∑ x, D.p x * F (Function.update s i x))]
  simp only [Fintype.sum_prod_type, hw, hu]
  calc ∑ x, ∑ r, D.p x * (∏ j, D.p (r j)) * F (e.symm (x, r))
      = ∑ r, ∑ x, (∏ j, D.p (r j)) * (D.p x * F (e.symm (x, r))) := by
        rw [sum_comm]; exact sum_congr rfl fun r _ => sum_congr rfl fun x _ => by ring
    _ = ∑ x', D.p x' * ∑ r, (∏ j, D.p (r j)) * ∑ x, D.p x * F (e.symm (x, r)) := by
        rw [← sum_mul, D.sum_one, one_mul]
        exact sum_congr rfl fun r _ => by rw [mul_sum]
    _ = _ := by
        refine sum_congr rfl fun x' _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun r _ => by ring

theorem g_sq_le (b : Bool) (z : ℝ) : g (bsign b) z ^ 2 ≤ 1 := by
  have h1 : 1 ≤ 1 + Real.exp (bsign b * z) := by linarith [Real.exp_pos (bsign b * z)]
  have hb : bsign b ^ 2 = 1 := by cases b <;> simp [bsign]
  rw [g, div_pow, div_le_one (by positivity), hb]
  nlinarith

/-- One step of the sampling recurrence: given the past, the next squared error grows by at most
`γ² Λ`. -/
theorem step_bound {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (u v : Vec m) :
    ∑ x, D.p x * ‖u + (γ * g (bsign (h x)) ⟪u, ψ x⟫) • ψ x - Pmap γ ψ h D v‖ ^ 2 ≤
      ‖u - v‖ ^ 2 + γ ^ 2 * (9 / 16) := by
  set c := Pmap γ ψ h D v
  set d := Pmap γ ψ h D u - u
  set N : Cube n → Vec m := fun x => (γ * g (bsign (h x)) ⟪u, ψ x⟫) • ψ x
  have hmean : ∑ x, D.p x • N x = d := by
    simp only [d, N, Pmap_eq_mean γ ψ h D u, smul_add, sum_add_distrib, ← sum_smul, D.sum_one,
      one_smul, add_sub_cancel_left]
  have hN : ∀ x, ‖N x‖ ^ 2 ≤ γ ^ 2 * (9 / 16) := by
    intro x
    simp only [N]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow]
    have := g_sq_le (h x) ⟪u, ψ x⟫
    have := hψ x
    calc γ ^ 2 * g (bsign (h x)) ⟪u, ψ x⟫ ^ 2 * ‖ψ x‖ ^ 2 ≤ γ ^ 2 * 1 * (9 / 16) := by gcongr
      _ = γ ^ 2 * (9 / 16) := by ring
  have hexp : ∀ x, ‖u + N x - c‖ ^ 2 = ‖N x‖ ^ 2 + 2 * ⟪N x, u - c⟫ + ‖u - c‖ ^ 2 := by
    intro x
    rw [show u + N x - c = N x + (u - c) by abel, norm_add_sq_real]
  have hcross : ∑ x, D.p x * ⟪N x, u - c⟫ = ⟪d, u - c⟫ := by
    rw [← hmean, sum_inner]
    exact sum_congr rfl fun x _ => (real_inner_smul_left (N x) (u - c) (D.p x)).symm
  have hPu : ‖Pmap γ ψ h D u - c‖ ^ 2 = ‖d‖ ^ 2 + 2 * ⟪d, u - c⟫ + ‖u - c‖ ^ 2 := by
    rw [show Pmap γ ψ h D u - c = d + (u - c) by simp only [d]; abel, norm_add_sq_real]
  have hP : ‖Pmap γ ψ h D u - c‖ ^ 2 ≤ ‖u - v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (Pmap_nonexpansive hγ0 hγ ψ hψ h D u v) 2
  have hsum : ∑ x, D.p x * ‖u + N x - c‖ ^ 2 =
      ∑ x, D.p x * ‖N x‖ ^ 2 + 2 * ⟪d, u - c⟫ + ‖u - c‖ ^ 2 := by
    simp only [hexp, mul_add, sum_add_distrib, ← sum_mul, D.sum_one, one_mul]
    rw [← hcross, mul_sum]
    congr 2
    exact sum_congr rfl fun x _ => by ring
  have hNs : ∑ x, D.p x * ‖N x‖ ^ 2 ≤ γ ^ 2 * (9 / 16) := by
    calc ∑ x, D.p x * ‖N x‖ ^ 2 ≤ ∑ x, D.p x * (γ ^ 2 * (9 / 16)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hN x) (D.nonneg x)
      _ = γ ^ 2 * (9 / 16) := by rw [← sum_mul, D.sum_one, one_mul]
  have hd := sq_nonneg ‖d‖
  show ∑ x, D.p x * ‖u + N x - c‖ ^ 2 ≤ _
  linarith

/-- Jensen's inequality for an average of vectors. -/
theorem norm_avg_sq_le {m : ℕ} (S : Finset ℕ) (hS : S.Nonempty) (d : ℕ → Vec m) :
    ‖((S.card : ℝ))⁻¹ • ∑ t ∈ S, d t‖ ^ 2 ≤ ((S.card : ℝ))⁻¹ * ∑ t ∈ S, ‖d t‖ ^ 2 := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h1 : ‖∑ t ∈ S, d t‖ ^ 2 ≤ S.card * ∑ t ∈ S, ‖d t‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (sq_sum_le_card_mul_sum_sq)
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  calc ((S.card : ℝ))⁻¹ ^ 2 * ‖∑ t ∈ S, d t‖ ^ 2
      ≤ ((S.card : ℝ))⁻¹ ^ 2 * (S.card * ∑ t ∈ S, ‖d t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

theorem tail_nonempty {T : ℕ} (hT : 1 ≤ T) : (tail T).Nonempty :=
  ⟨T, by simp only [tail, Finset.mem_Icc]; omega⟩

theorem tailAvg_sub {m T : ℕ} (u v : ℕ → Vec m) :
    tailAvg T u - tailAvg T v = tailAvg T (fun t => u t - v t) := by
  simp only [tailAvg, sum_sub_distrib, smul_sub]

end Population

/-- Sampling and label effects (`lem:population`), sampling part: `E ‖u_t - v_t‖² ≤ t γ² Λ` for every initial vector,
where the expectation is over histories drawn from `D^T` and `t ≤ T`. -/
theorem frozen_sq_error {n m T : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (t : ℕ) (ht : t ≤ T) :
    ∑ s : Fin T → Cube n, histWeight D s *
        ‖frozen γ ψ (ext s) (labels h (ext s)) b0 t - (Pmap γ ψ h D)^[t] b0‖ ^ 2
      ≤ t * γ ^ 2 * (9 / 16) := by
  induction t with
  | zero => simp [frozen]
  | succ t ih =>
    have htT : t < T := by omega
    let i : Fin T := ⟨t, htT⟩
    have hupd : ∀ (s : Fin T → Cube n) (x : Cube n),
        frozen γ ψ (ext (Function.update s i x)) (labels h (ext (Function.update s i x))) b0
            (t + 1) =
          frozen γ ψ (ext s) (labels h (ext s)) b0 t +
            (γ * g (bsign (h x)) ⟪frozen γ ψ (ext s) (labels h (ext s)) b0 t, ψ x⟫) • ψ x := by
      intro s x
      have hxs : ∀ k < t, ext (Function.update s i x) k = ext s k := by
        intro k hk
        have hne : (⟨k, by omega⟩ : Fin T) ≠ i := by
          intro he; have := congrArg Fin.val he; simp [i] at this; omega
        have hkT : k < T := by omega
        simp only [ext, hkT, dite_true]
        rw [Function.update_of_ne hne]
      have hxt : ext (Function.update s i x) t = x := by
        simp only [ext, htT, dite_true]
        exact Function.update_self i x s
      simp only [frozen]
      rw [frozen_congr γ ψ b0 t (xs' := ext s) (ys' := labels h (ext s)) hxs
        (fun k hk => by simp only [labels, hxs k hk])]
      simp only [labels, hxt]
    rw [sum_histWeight_update D i, Function.iterate_succ_apply']
    simp only [hupd]
    refine (sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (step_bound hγ0 hγ ψ hψ h D _ ((Pmap γ ψ h D)^[t] b0)) (histWeight_nonneg D s)).trans ?_
    simp only [mul_add, sum_add_distrib, ← sum_mul, sum_histWeight, one_mul]
    have := ih (by omega)
    push_cast
    linarith

/-- Sampling and label effects (`lem:population`), label part: `‖v_t - z_t‖ ≤ t γ ‖μ‖ / 2`. -/
theorem label_effect {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (t : ℕ) :
    ‖(Pmap γ ψ h D)^[t] b0 - (Rmap γ ψ D)^[t] b0‖ ≤ t * γ * ‖mu ψ h D‖ / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have he : Pmap γ ψ h D ((Pmap γ ψ h D)^[t] b0) - Rmap γ ψ D ((Rmap γ ψ D)^[t] b0) =
        (Rmap γ ψ D ((Pmap γ ψ h D)^[t] b0) - Rmap γ ψ D ((Rmap γ ψ D)^[t] b0)) +
          (γ / 2) • mu ψ h D := by
      simp only [Pmap]; abel
    rw [he]
    calc _ ≤ ‖Rmap γ ψ D ((Pmap γ ψ h D)^[t] b0) - Rmap γ ψ D ((Rmap γ ψ D)^[t] b0)‖ +
          ‖(γ / 2) • mu ψ h D‖ := norm_add_le _ _
      _ ≤ ‖(Pmap γ ψ h D)^[t] b0 - (Rmap γ ψ D)^[t] b0‖ + γ / 2 * ‖mu ψ h D‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          gcongr
          exact Rmap_nonexpansive hγ0 hγ ψ hψ D _ _
      _ ≤ t * γ * ‖mu ψ h D‖ / 2 + γ / 2 * ‖mu ψ h D‖ := by linarith
      _ = ((t + 1 : ℕ) : ℝ) * γ * ‖mu ψ h D‖ / 2 := by push_cast; ring

/-- Sampling and label effects (`lem:population`), tail sampling part: `E ‖ū - v̄‖² ≤ Λ B² / T` with `B = γ T`. -/
theorem tail_sq_error {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) :
    ∑ s : Fin T → Cube n, histWeight D s *
        ‖tailAvg T (frozen γ ψ (ext s) (labels h (ext s)) b0) -
          tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0)‖ ^ 2
      ≤ 9 / 16 * (γ * T) ^ 2 / T := by
  have hne := tail_nonempty hT
  have hc : (0 : ℝ) < (tail T).card := by exact_mod_cast hne.card_pos
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [tailAvg_sub]
  calc ∑ s : Fin T → Cube n, histWeight D s *
        ‖tailAvg T (fun t => frozen γ ψ (ext s) (labels h (ext s)) b0 t -
          (Pmap γ ψ h D)^[t] b0)‖ ^ 2
      ≤ ∑ s : Fin T → Cube n, histWeight D s * (((tail T).card : ℝ)⁻¹ * ∑ t ∈ tail T,
          ‖frozen γ ψ (ext s) (labels h (ext s)) b0 t - (Pmap γ ψ h D)^[t] b0‖ ^ 2) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (norm_avg_sq_le _ hne _)
          (histWeight_nonneg D s)
    _ = ((tail T).card : ℝ)⁻¹ * ∑ t ∈ tail T, ∑ s : Fin T → Cube n, histWeight D s *
          ‖frozen γ ψ (ext s) (labels h (ext s)) b0 t - (Pmap γ ψ h D)^[t] b0‖ ^ 2 := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ ≤ ((tail T).card : ℝ)⁻¹ * ∑ t ∈ tail T, (T * γ ^ 2 * (9 / 16) : ℝ) := by
        gcongr with t ht
        have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
        refine (frozen_sq_error hγ0 hγ ψ hψ h D b0 t htT).trans ?_
        gcongr
    _ = 9 / 16 * (γ * T) ^ 2 / T := by
        rw [sum_const, nsmul_eq_mul]
        field_simp

/-- Sampling and label effects (`lem:population`), tail label part: `|⟪v̄ - z̄, ψ(x)⟫| ≤ 3 B ‖μ‖ / 8` with `B = γ T`. -/
theorem tail_label_effect {n m T : ℕ} (hT : 1 ≤ T) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (h : Cube n → Bool) (D : Dist n)
    (b0 : Vec m) (x : Cube n) :
    |⟪tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0) - tailAvg T (fun t => (Rmap γ ψ D)^[t] b0),
        ψ x⟫| ≤ 3 * (γ * T) / 8 * ‖mu ψ h D‖ := by
  have hne := tail_nonempty hT
  have hc : (0 : ℝ) < (tail T).card := by exact_mod_cast hne.card_pos
  have hψx : ‖ψ x‖ ≤ 3 / 4 := by
    have := hψ x; have := norm_nonneg (ψ x); nlinarith
  have hμ := norm_nonneg (mu ψ h D)
  have havg : ‖tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0) -
      tailAvg T (fun t => (Rmap γ ψ D)^[t] b0)‖ ≤ T * γ * ‖mu ψ h D‖ / 2 := by
    rw [tailAvg_sub, tailAvg, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ((tail T).card : ℝ)⁻¹ *
          ‖∑ t ∈ tail T, ((Pmap γ ψ h D)^[t] b0 - (Rmap γ ψ D)^[t] b0)‖
        ≤ ((tail T).card : ℝ)⁻¹ * ∑ t ∈ tail T, (T * γ * ‖mu ψ h D‖ / 2 : ℝ) := by
          gcongr
          refine (norm_sum_le _ _).trans (sum_le_sum fun t ht => ?_)
          refine (label_effect hγ0 hγ ψ hψ h D b0 t).trans ?_
          have htT : (t : ℝ) ≤ T := by exact_mod_cast (Finset.mem_Icc.mp ht).2
          gcongr
      _ = T * γ * ‖mu ψ h D‖ / 2 := by
          rw [sum_const, nsmul_eq_mul]; field_simp
  calc _ ≤ ‖tailAvg T (fun t => (Pmap γ ψ h D)^[t] b0) -
        tailAvg T (fun t => (Rmap γ ψ D)^[t] b0)‖ * ‖ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (T * γ * ‖mu ψ h D‖ / 2) * (3 / 4) :=
        mul_le_mul havg hψx (norm_nonneg _) (by positivity)
    _ = 3 * (γ * T) / 8 * ‖mu ψ h D‖ := by ring

end GaussianSGD
