import GaussianSGD.Defs

/-!
# Auxiliary lemmas for the risk bound

Measurability and continuity of the comparison objects, the layer-cake bound behind the
estimate `24 d + 48 σ` in the proof of Risk controlled by kernel correlation (`thm:risk`),
the pathwise disagreement bound, and the change of variables `b₀ = √m a₀`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set

namespace GaussianSGD.RiskAux

theorem continuous_tanh : Continuous Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    funext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

theorem continuous_Rmap {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) :
    Continuous (Rmap γ ψ D) := by
  unfold Rmap
  have := continuous_tanh
  fun_prop

theorem continuous_Zsym {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ)
    (x : Cube n) : Continuous (fun b => Zsym γ ψ D T x b) := by
  unfold Zsym tailAvg
  have h := continuous_Rmap γ ψ D
  have : ∀ t, Continuous ((Rmap γ ψ D)^[t]) := fun t => h.iterate t
  fun_prop

lemma continuous_psi {n m : ℕ} (x : Cube n) : Continuous (fun W : Fin m → Vec n => psi W x) := by
  unfold psi hid relu
  fun_prop

lemma measurableSet_good (n m : ℕ) : MeasurableSet {W : Fin m → Vec n | Good W} := by
  refine IsClosed.measurableSet ?_
  simp only [Good, ofPred_forall, ofPred_and]
  exact isClosed_iInter fun x =>
    (isClosed_le continuous_const ((continuous_psi x).norm.pow 2)).inter
      (isClosed_le ((continuous_psi x).norm.pow 2) continuous_const)

lemma inv_sqrt_eqOn (a b : ℝ) :
    EqOn (fun t : ℝ => a + b * t ^ (-(1 / 2 : ℝ))) (fun t => a + b / Real.sqrt t) (uIcc 0 1) := by
  intro t ht
  have ht0 : 0 ≤ t := by
    rw [uIcc_of_le zero_le_one] at ht; exact ht.1
  simp only
  rw [Real.rpow_neg ht0, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

lemma intervalIntegrable_inv_sqrt (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => a + b / Real.sqrt t) volume 0 1 :=
  (intervalIntegrable_const.add
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul b)).congr_uIoo
    ((inv_sqrt_eqOn a b).mono (by
      rw [uIoo_of_le zero_le_one, uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self))

/-- `∫₀¹ (a + b/√t) dt = a + 2b`. -/
theorem integral_inv_sqrt (a b : ℝ) :
    ∫ t in (0 : ℝ)..1, (a + b / Real.sqrt t) = a + 2 * b := by
  rw [← intervalIntegral.integral_congr (inv_sqrt_eqOn a b), intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  · norm_num; ring
  · exact intervalIntegrable_const
  · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul b

theorem lintegral_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (a + b / Real.sqrt t) = ENNReal.ofReal (a + 2 * b) := by
  rw [← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le zero_le_one,
    integral_inv_sqrt]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegrable_inv_sqrt a b)
  · exact ae_of_all _ (fun t => add_nonneg ha (div_nonneg hb (Real.sqrt_nonneg t)))

/-- The bound `min {1, σ²/(|z| - d)²}` on a disagreement probability, set to `1` when
`|z| ≤ d`. -/
def disBound (d σ z : ℝ) : ℝ := if d < |z| then min 1 (σ ^ 2 / (|z| - d) ^ 2) else 1

lemma disBound_nonneg (d σ z : ℝ) : 0 ≤ disBound d σ z := by
  unfold disBound; split_ifs
  · exact le_min zero_le_one (by positivity)
  · exact zero_le_one

lemma disBound_le_one (d σ z : ℝ) : disBound d σ z ≤ 1 := by
  unfold disBound; split_ifs
  · exact min_le_left _ _
  · exact le_rfl

lemma measurable_disBound (d σ : ℝ) : Measurable (disBound d σ) := by
  unfold disBound
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id.abs) ?_ measurable_const
  fun_prop

lemma abs_le_of_lt_disBound {d σ z t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (h : t < disBound d σ z) :
    |z| ≤ d + σ / Real.sqrt t := by
  unfold disBound at h
  split_ifs at h with hz
  · have hu : 0 < |z| - d := sub_pos.2 hz
    have h1 : t < σ ^ 2 / (|z| - d) ^ 2 := lt_of_lt_of_le h (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have h2 : Real.sqrt t * (|z| - d) < σ := by
      refine lt_of_pow_lt_pow_left₀ 2 hσ ?_
      rw [mul_pow, Real.sq_sqrt ht.le]; exact h1
    have h3 : |z| - d < σ / Real.sqrt t := by
      rw [lt_div_iff₀ hst]; linarith
    linarith
  · have : 0 ≤ σ / Real.sqrt t := div_nonneg hσ (Real.sqrt_nonneg t)
    linarith

/-- Layer-cake bound: if `Z` has small-ball probability at most `c r` on `[-r, r]`, then the
expectation of `disBound d σ Z` is at most `c d + 2 c σ`. -/
theorem lintegral_disBound_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {Z : α → ℝ}
    (hZ : Measurable Z) {c d σ : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hσ : 0 ≤ σ)
    (hsb : ∀ r, 0 ≤ r → μ {a | |Z a| ≤ r} ≤ ENNReal.ofReal (c * r)) :
    ∫⁻ a, ENNReal.ofReal (disBound d σ (Z a)) ∂μ ≤ ENNReal.ofReal (c * d + 2 * (c * σ)) := by
  rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ fun a => disBound_nonneg d σ (Z a))
    ((measurable_disBound d σ).comp hZ).aemeasurable]
  calc ∫⁻ t in Ioi 0, μ {a | t < disBound d σ (Z a)}
      ≤ ∫⁻ t in Ioi 0, (Iic 1).indicator
          (fun t => ENNReal.ofReal (c * d + (c * σ) / Real.sqrt t)) t := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        by_cases ht1 : t ≤ 1
        · rw [indicator_of_mem (show t ∈ Iic 1 from ht1)]
          have hr : 0 ≤ d + σ / Real.sqrt t := add_nonneg hd (div_nonneg hσ (Real.sqrt_nonneg t))
          refine (measure_mono fun a ha => ?_).trans ((hsb _ hr).trans_eq ?_)
          · exact abs_le_of_lt_disBound hσ ht ha
          · rw [mul_add, mul_div_assoc]
        · rw [indicator_of_notMem (show t ∉ Iic 1 from ht1)]
          have he : {a | t < disBound d σ (Z a)} = ∅ := by
            ext a
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
            exact (disBound_le_one _ _ _).trans (not_le.1 ht1).le
          rw [he, measure_empty]
    _ = ENNReal.ofReal (c * d + 2 * (c * σ)) := by
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
          inter_comm, Ioi_inter_Iic]
        exact lintegral_inv_sqrt (mul_nonneg hc hd) (mul_nonneg hc hσ)

lemma abs_le_abs_sub_of_sgn_ne {F Z : ℝ} (h : sgn F ≠ sgn Z) : |Z| ≤ |F - Z| := by
  unfold sgn at h
  split_ifs at h with h1 h2 h2
  · exact absurd rfl h
  · rw [abs_of_neg (not_le.1 h2), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg h2, abs_of_nonpos (by linarith)]; linarith
  · exact absurd rfl h

lemma histWeight_nonneg {n T : ℕ} (D : Dist n) (s : Fin T → Cube n) : 0 ≤ histWeight D s :=
  Finset.prod_nonneg fun i _ => D.nonneg (s i)

lemma sum_histWeight {n T : ℕ} (D : Dist n) : ∑ s : Fin T → Cube n, histWeight D s = 1 := by
  unfold histWeight
  rw [← Fintype.prod_sum (fun (_ : Fin T) x => D.p x)]
  simp [D.sum_one]

/-- If `|F_i - Z| ≤ d + |E_i|` for every `i` and `∑ w_i E_i² ≤ σ²`, the `w`-probability
that `sgn F_i ≠ sgn Z` is at most `disBound d σ Z`. -/
lemma sum_disagree_le {ι : Type*} (s : Finset ι) {w F E : ι → ℝ} {Z d σ : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hFZ : ∀ i, |F i - Z| ≤ d + |E i|)
    (hE : ∑ i ∈ s, w i * E i ^ 2 ≤ σ ^ 2) :
    ∑ i ∈ s, w i * (if sgn (F i) = sgn Z then 0 else 1) ≤ disBound d σ Z := by
  have hle1 : ∑ i ∈ s, w i * (if sgn (F i) = sgn Z then 0 else 1) ≤ 1 := by
    refine le_of_le_of_eq (Finset.sum_le_sum fun i _ => ?_) hw1
    calc w i * (if sgn (F i) = sgn Z then 0 else 1) ≤ w i * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (hw i)
          split_ifs <;> norm_num
      _ = w i := mul_one _
  unfold disBound
  split_ifs with hZ
  · refine le_min hle1 ?_
    have hu : 0 < |Z| - d := sub_pos.2 hZ
    calc ∑ i ∈ s, w i * (if sgn (F i) = sgn Z then 0 else 1)
        ≤ ∑ i ∈ s, w i * (E i ^ 2 / (|Z| - d) ^ 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
          split_ifs with hs
          · positivity
          · have h1 := abs_le_abs_sub_of_sgn_ne hs
            have h2 : |Z| - d ≤ |E i| := by linarith [hFZ i]
            rw [le_div_iff₀ (by positivity), one_mul, ← sq_abs (E i)]
            exact pow_le_pow_left₀ hu.le h2 2
      _ = (∑ i ∈ s, w i * E i ^ 2) / (|Z| - d) ^ 2 := by
          rw [Finset.sum_div]; congr 1; ext i; ring
      _ ≤ σ ^ 2 / (|Z| - d) ^ 2 := by gcongr
  · exact hle1

/-- The error decomposition `err(G) ≥ err(S) - Pr_D[G ≠ S]`. -/
lemma err_ge {n : ℕ} (D : Dist n) (G S : Cube n → ℝ) (h : Cube n → Bool) :
    err D S h - ∑ x, D.p x * (if G x = S x then 0 else 1) ≤ err D G h := by
  unfold err
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (D.nonneg x)
  split_ifs <;> simp_all

lemma labels_pm {n : ℕ} (h : Cube n → Bool) (xs : ℕ → Cube n) (t : ℕ) :
    labels h xs t = 1 ∨ labels h xs t = -1 := by
  unfold labels bsign; split_ifs <;> simp

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma err_nonneg {n : ℕ} (D : Dist n) (G : Cube n → ℝ) (h : Cube n → Bool) : 0 ≤ err D G h :=
  Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (by split_ifs <;> norm_num)

lemma err_le_one {n : ℕ} (D : Dist n) (G : Cube n → ℝ) (h : Cube n → Bool) : err D G h ≤ 1 := by
  refine le_of_le_of_eq (Finset.sum_le_sum fun x _ => ?_) D.sum_one
  calc D.p x * (if G x = bsign (h x) then 0 else 1) ≤ D.p x * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (D.nonneg x)
        split_ifs <;> norm_num
    _ = D.p x := mul_one _

lemma condErr_nonneg {n m : ℕ} (η : ℝ) (T : ℕ) (θ0 : Params n m) (h : Cube n → Bool)
    (D : Dist n) : 0 ≤ condErr η T θ0 h D :=
  Finset.sum_nonneg fun s _ => mul_nonneg (histWeight_nonneg D s) (err_nonneg _ _ _)

lemma measurable_err_comp {α : Type*} [MeasurableSpace α] {n : ℕ} (D : Dist n)
    (h : Cube n → Bool) {Z : Cube n → α → ℝ} (hZ : ∀ x, Measurable (Z x)) :
    Measurable (fun b => err D (fun x => sgn (Z x b)) h) := by
  unfold err
  refine Finset.measurable_sum _ fun x _ => measurable_const.mul ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_sgn.comp (hZ x)) (measurableSet_singleton _)

lemma ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  refine (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans ?_
  exact ENNReal.ofReal_toReal_le

lemma integral_disBound_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {Z : α → ℝ}
    (hZ : Measurable Z) {c d σ : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hσ : 0 ≤ σ)
    (hsb : ∀ r, 0 ≤ r → μ {a | |Z a| ≤ r} ≤ ENNReal.ofReal (c * r)) :
    ∫ a, disBound d σ (Z a) ∂μ ≤ c * d + 2 * (c * σ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun a => disBound_nonneg d σ (Z a))
    ((measurable_disBound d σ).comp hZ).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_disBound_le μ hZ hc hd hσ hsb)

/-- Change of variables `a₀ = m^{-1/2} b₀` with `b₀ ∼ N(0, I_m)`. -/
lemma lintegral_outLaw {m : ℕ} (hm : 0 < m) (f : Vec m → ENNReal) :
    ∫⁻ a, f a ∂(outLaw m) = ∫⁻ b, f ((Real.sqrt m)⁻¹ • b) ∂(stdGaussian (Vec m)) := by
  have hc : (Real.sqrt m)⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne'
  unfold outLaw
  rw [show (fun v : Vec m => (Real.sqrt m)⁻¹ • v) = ⇑(MeasurableEquiv.smul₀ _ hc) from rfl,
    lintegral_map_equiv]
  rfl

lemma stdGaussian_norm_gt {m : ℕ} :
    stdGaussian (Vec m) {b | 2 < ‖(Real.sqrt m)⁻¹ • b‖} = outLaw m {a | 2 < ‖a‖} := by
  unfold outLaw
  rw [Measure.map_apply (measurable_const_smul _) (measurableSet_lt measurable_const
    measurable_norm)]
  rfl

/-- The label-weighted ReLU feature average `E_D h(x) ReLU⟪w, x⟫`. -/
def corrFn {n : ℕ} (h : Cube n → Bool) (D : Dist n) (w : Vec n) : ℝ :=
  ∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫

lemma mu_apply {n m : ℕ} (W : Fin m → Vec n) (h : Cube n → Bool) (D : Dist n) (j : Fin m) :
    mu (psi W) h D j = (Real.sqrt m)⁻¹ * corrFn h D (W j) := by
  simp only [mu, psi, hid, corrFn, Finset.mul_sum]
  simp
  exact Finset.sum_congr rfl fun x _ => by ring

lemma norm_mu_sq {n m : ℕ} (W : Fin m → Vec n) (h : Cube n → Bool) (D : Dist n) :
    ‖mu (psi W) h D‖ ^ 2 = ∑ j, (m : ℝ)⁻¹ * corrFn h D (W j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs, mu_apply, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]


end GaussianSGD.RiskAux
