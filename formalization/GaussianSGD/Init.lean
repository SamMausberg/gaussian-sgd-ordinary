import GaussianSGD.Defs

/-!
# Initialization bounds (`lem:init`)
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

instance isProbabilityMeasure_rowLaw (n : ℕ) : IsProbabilityMeasure (rowLaw n) := by
  unfold rowLaw; infer_instance

instance isProbabilityMeasure_hiddenLaw (n m : ℕ) : IsProbabilityMeasure (hiddenLaw n m) := by
  unfold hiddenLaw; infer_instance

instance isProbabilityMeasure_outLaw (m : ℕ) : IsProbabilityMeasure (outLaw m) := by
  unfold outLaw; infer_instance

namespace InitAux

lemma continuous_relu : Continuous relu := continuous_id.max continuous_const

lemma norm_pt_sq {n : ℕ} (x : Cube n) : ‖pt x‖ ^ 2 = n := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [pt, bsign]

/-- The law of `⟪w, v⟫` for `w ∼ N(0, I_n/n)` is `N(0, ‖v‖²/n)`. -/
lemma rowLaw_map_inner {n : ℕ} (v : Vec n) :
    (rowLaw n).map (fun w => ⟪w, v⟫) = gaussianReal 0 (‖v‖ ^ 2 / n).toNNReal := by
  set c : ℝ := (Real.sqrt n)⁻¹
  have hcomp : (fun w : Vec n => ⟪w, v⟫) ∘ (fun u : Vec n => c • u) = ⇑(innerSL ℝ (c • v)) := by
    funext u
    simp [real_inner_smul_right, real_inner_comm]
  rw [rowLaw, Measure.map_map (by fun_prop) (by fun_prop), hcomp,
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg n), div_eq_inv_mul]

/-- At a cube point, `⟪w, x⟫ ∼ N(0,1)` for `w ∼ N(0, I_n/n)`. -/
lemma rowLaw_map_inner_pt {n : ℕ} (hn : 1 ≤ n) (x : Cube n) :
    (rowLaw n).map (fun w => ⟪w, pt x⟫) = gaussianReal 0 1 := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [rowLaw_map_inner, norm_pt_sq, div_self hn']
  simp

/-- `E e^{t Z²} = (1 - 2t)^{-1/2}` for `Z ∼ N(0,1)` and `t < 1/2`. -/
lemma lintegral_exp_mul_sq {t : ℝ} (ht : t < 1 / 2) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * z ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t))) := by
  have hb : 0 < 1 / 2 - t := by linarith
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  have hpt : ∀ z : ℝ, (gaussianPDF 0 1 * fun z => ENNReal.ofReal (Real.exp (t * z ^ 2))) z =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * z ^ 2)) := by
    intro z
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun z => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- `E e^{t ReLU(Z)²} = (1 + (1 - 2t)^{-1/2}) / 2` for `Z ∼ N(0,1)` and `t < 1/2`. -/
lemma lintegral_exp_mul_relu_sq {t : ℝ} (ht : t < 1 / 2) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * relu z ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal ((1 + Real.sqrt (1 / (1 - 2 * t))) / 2) := by
  set f : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (t * relu z ^ 2))
  have hf : Measurable f := by
    have := continuous_relu
    fun_prop
  have hneg : ∫⁻ z, f (-z) ∂(gaussianReal 0 1) = ∫⁻ z, f z ∂(gaussianReal 0 1) := by
    rw [← lintegral_map hf measurable_neg, gaussianReal_map_neg, neg_zero]
  have hsum : ∀ z, f z + f (-z) = ENNReal.ofReal (Real.exp (t * z ^ 2)) + 1 := by
    intro z
    rcases le_total 0 z with hz | hz
    · simp [f, relu, max_eq_left hz, max_eq_right (neg_nonpos.2 hz)]
    · simp [f, relu, max_eq_right hz, max_eq_left (neg_nonneg.2 hz), add_comm]
  have h2 : 2 * ∫⁻ z, f z ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t))) + 1 := by
    rw [two_mul]
    nth_rw 2 [← hneg]
    rw [← lintegral_add_left hf]
    simp_rw [hsum]
    rw [lintegral_add_right _ measurable_const, lintegral_exp_mul_sq ht]
    simp
  have h2' : (2 : ENNReal) * ENNReal.ofReal ((1 + Real.sqrt (1 / (1 - 2 * t))) / 2) =
      ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t))) + 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by positivity) zero_le_one]
    congr 1
    ring
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 (h2.trans h2'.symm)

/-- For i.i.d. coordinates, the integral of a product is the power of the integral. -/
lemma lintegral_pi_prod {ι α : Type*} [Fintype ι] [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ENNReal} (hf : Measurable f) :
    ∫⁻ ω, ∏ i, f (ω i) ∂(Measure.pi fun _ : ι => μ) = (∫⁻ a, f a ∂μ) ^ Fintype.card ι := by
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.pi fun _ : ι => μ)
    Finset.univ (fun i (ω : ι → α) => f (ω i))
    (iIndepFun_pi (X := fun _ => f) fun _ => hf.aemeasurable)
    (fun i => hf.comp (measurable_pi_apply i))
  rw [h]
  simp_rw [(measurePreserving_eval (fun _ : ι => μ) _).lintegral_comp hf]
  simp

lemma norm_psi_sq {n m : ℕ} (W : Fin m → Vec n) (x : Cube n) :
    ‖psi W x‖ ^ 2 = (m : ℝ)⁻¹ * ∑ j, relu ⟪W j, pt x⟫ ^ 2 := by
  rw [psi, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg m), hid, EuclideanSpace.real_norm_sq_eq]

/-- Chernoff bound for `θ ∑_j ReLU⟪W_j, x⟫²` under the hidden-layer law. -/
lemma chernoff_hidden {n m : ℕ} (hn : 1 ≤ n) (x : Cube n) {θ : ℝ} (hθ : θ < 1 / 2) (a : ℝ) :
    hiddenLaw n m {W | a ≤ θ * ∑ j, relu ⟪W j, pt x⟫ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-a) * ((1 + Real.sqrt (1 / (1 - 2 * θ))) / 2) ^ m) := by
  set S : (Fin m → Vec n) → ℝ := fun W => θ * ∑ j, relu ⟪W j, pt x⟫ ^ 2 with hS
  set M : ℝ := (1 + Real.sqrt (1 / (1 - 2 * θ))) / 2
  have hrelu := continuous_relu
  have hf : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (θ * relu z ^ 2)) := by fun_prop
  have hrow : ∫⁻ w, ENNReal.ofReal (Real.exp (θ * relu ⟪w, pt x⟫ ^ 2)) ∂(rowLaw n) =
      ENNReal.ofReal M := by
    rw [← lintegral_exp_mul_relu_sq hθ, ← rowLaw_map_inner_pt hn x, lintegral_map hf (by fun_prop)]
  have hint : ∫⁻ W, ENNReal.ofReal (Real.exp (S W)) ∂(hiddenLaw n m) = ENNReal.ofReal M ^ m := by
    have hprod : ∀ W : Fin m → Vec n, ENNReal.ofReal (Real.exp (S W)) =
        ∏ j, ENNReal.ofReal (Real.exp (θ * relu ⟪W j, pt x⟫ ^ 2)) := by
      intro W
      simp only [hS]
      rw [Finset.mul_sum, Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    simp_rw [hprod]
    have hg : Measurable fun w : Vec n => ENNReal.ofReal (Real.exp (θ * relu ⟪w, pt x⟫ ^ 2)) :=
      hf.comp (by fun_prop : Measurable fun w : Vec n => ⟪w, pt x⟫)
    rw [hiddenLaw, lintegral_pi_prod (ι := Fin m) (rowLaw n) hg, hrow, Fintype.card_fin]
  have hmeas : Measurable fun W : Fin m → Vec n => ENNReal.ofReal (Real.exp (S W)) := by
    simp only [hS]; fun_prop
  have hsub : {W | a ≤ S W} ⊆ {W | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (S W))} :=
    fun W hW => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hW)
  calc hiddenLaw n m {W | a ≤ S W}
      = ENNReal.ofReal (Real.exp (-a)) *
          (ENNReal.ofReal (Real.exp a) * hiddenLaw n m {W | a ≤ S W}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-a)) * (ENNReal.ofReal (Real.exp a) *
          hiddenLaw n m {W | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (S W))}) := by
        gcongr
    _ ≤ ENNReal.ofReal (Real.exp (-a)) *
          ∫⁻ W, ENNReal.ofReal (Real.exp (S W)) ∂(hiddenLaw n m) := by
        gcongr
        exact mul_meas_ge_le_lintegral₀ hmeas.aemeasurable _
    _ = ENNReal.ofReal (Real.exp (-a) * M ^ m) := by
        rw [hint, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (by positivity)]

lemma exp_pow_le {m : ℕ} {a b M : ℝ} (hM : 0 ≤ M) (h : Real.exp (-a) * M ≤ Real.exp (-b)) :
    Real.exp (-(a * m)) * M ^ m ≤ Real.exp (-(b * m)) := by
  have h1 : ∀ c : ℝ, Real.exp (-(c * m)) = Real.exp (-c) ^ m := by
    intro c; rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h1, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h m

/-- Upper tail of `‖ψ(x)‖²` at distance `1/16` from the mean `1/2`, with `θ = 1/512`. -/
lemma upper_tail {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Cube n) :
    hiddenLaw n m {W | 9 / 16 < ‖psi W x‖ ^ 2} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) / 16384)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine (measure_mono ?_).trans ((chernoff_hidden (m := m) hn x
    (θ := 1 / 512) (by norm_num) (9 / 8192 * m)).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro W hW
    simp only [Set.mem_ofPred_eq, norm_psi_sq] at hW ⊢
    rw [lt_inv_mul_iff₀ hm'] at hW
    linarith
  · refine (exp_pow_le (b := 1 / 16384) (by positivity) ?_).trans_eq (by ring_nf)
    have hs : Real.sqrt (1 / (1 - 2 * (1 / 512))) ≤ 1 + 34 / 16384 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have he : 1 + 17 / 16384 ≤ Real.exp (17 / 16384) := by
      have := Real.add_one_le_exp (17 / 16384); linarith
    calc Real.exp (-(9 / 8192)) * ((1 + Real.sqrt (1 / (1 - 2 * (1 / 512)))) / 2)
        ≤ Real.exp (-(9 / 8192)) * Real.exp (17 / 16384) := by
          gcongr; linarith
      _ = Real.exp (-(1 / 16384)) := by rw [← Real.exp_add]; norm_num

/-- Lower tail of `‖ψ(x)‖²` at distance `1/16` from the mean `1/2`, with `θ = -1/512`. -/
lemma lower_tail {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (x : Cube n) :
    hiddenLaw n m {W | ‖psi W x‖ ^ 2 < 7 / 16} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) / 16384)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine (measure_mono ?_).trans ((chernoff_hidden (m := m) hn x
    (θ := -(1 / 512)) (by norm_num) (-(7 / 8192) * m)).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro W hW
    simp only [Set.mem_ofPred_eq, norm_psi_sq] at hW ⊢
    rw [inv_mul_lt_iff₀ hm'] at hW
    linarith
  · refine (exp_pow_le (b := 1 / 16384) (by positivity) ?_).trans_eq (by ring_nf)
    have hs : Real.sqrt (1 / (1 - 2 * -(1 / 512))) ≤ 1 - 30 / 16384 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have he : 1 - 15 / 16384 ≤ Real.exp (-(15 / 16384)) := by
      have := Real.add_one_le_exp (-(15 / 16384)); linarith
    calc Real.exp (-(-(7 / 8192))) * ((1 + Real.sqrt (1 / (1 - 2 * -(1 / 512)))) / 2)
        ≤ Real.exp (-(-(7 / 8192))) * Real.exp (-(15 / 16384)) := by
          gcongr; linarith
      _ = Real.exp (-(1 / 16384)) := by rw [← Real.exp_add]; norm_num

end InitAux

open InitAux

/-- Initialization bounds (`lem:init`), hidden layer: `Pr(W₀ ∉ 𝒢) ≤ ρ_W`. -/
theorem init_hidden {n m : ℕ} (hn : 1 ≤ n) :
    hiddenLaw n m {W | ¬ Good W} ≤ ENNReal.ofReal (rhoW n m) := by
  set e : ℝ := Real.exp (-(m : ℝ) / 16384)
  have hmain : hiddenLaw n m {W | ¬ Good W} ≤ ENNReal.ofReal (2 ^ (n + 1) * e) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine prob_le_one.trans ?_
      simp only [e, CharP.cast_eq_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
    have hsub : {W : Fin m → Vec n | ¬ Good W} ⊆
        ⋃ x : Cube n, ({W | ‖psi W x‖ ^ 2 < 7 / 16} ∪ {W | 9 / 16 < ‖psi W x‖ ^ 2}) := by
      intro W hW
      simp only [Good, not_forall, not_and_or, not_le, Set.mem_ofPred_eq] at hW
      obtain ⟨x, hx⟩ := hW
      exact Set.mem_iUnion.2 ⟨x, hx⟩
    calc hiddenLaw n m {W | ¬ Good W}
        ≤ ∑ x : Cube n,
            hiddenLaw n m ({W | ‖psi W x‖ ^ 2 < 7 / 16} ∪ {W | 9 / 16 < ‖psi W x‖ ^ 2}) :=
          (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _x : Cube n, (ENNReal.ofReal e + ENNReal.ofReal e) := by
          refine Finset.sum_le_sum fun x _ => (measure_union_le _ _).trans ?_
          exact add_le_add (lower_tail hn hm x) (upper_tail hn hm x)
      _ = ENNReal.ofReal (2 ^ (n + 1) * e) := by
          rw [Finset.sum_const, Finset.card_univ,
            ← ENNReal.ofReal_add (by positivity) (by positivity), nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          simp [pow_succ]
          ring
  rw [rhoW, ENNReal.ofReal_min, ENNReal.ofReal_one]
  exact le_min prob_le_one hmain

/-- Initialization bounds (`lem:init`), output layer: `Pr(‖a₀‖ > 2) ≤ ρ_a`. -/
theorem init_output (m : ℕ) : outLaw m {a | 2 < ‖a‖} ≤ ENNReal.ofReal (rhoA m) := by
  set μ := stdGaussian (Vec m)
  set g : Vec m → ENNReal := fun b => ENNReal.ofReal (Real.exp (‖b‖ ^ 2 / 4))
  have hg : Measurable g := by fun_prop
  have hset : outLaw m {a | 2 < ‖a‖} ≤ μ {b | (m : ℝ) ≤ ‖b‖ ^ 2 / 4} := by
    rw [outLaw, Measure.map_apply (by fun_prop) (measurableSet_lt measurable_const measurable_norm)]
    refine measure_mono fun b hb => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)] at hb ⊢
    have hc : 0 < (Real.sqrt m)⁻¹ := by
      by_contra hc
      have : (Real.sqrt m)⁻¹ * ‖b‖ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) (norm_nonneg b)
      linarith
    have hsq : 0 < Real.sqrt m := inv_pos.1 hc
    rw [lt_inv_mul_iff₀ hsq] at hb
    have h4 : (2 * Real.sqrt m) ^ 2 = 4 * m := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; ring
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hint : ∫⁻ b, g b ∂μ = ENNReal.ofReal (Real.sqrt 2) ^ m := by
    rw [show μ = (Measure.pi fun _ : Fin m => gaussianReal 0 1).map (WithLp.toLp 2) from
      map_pi_eq_stdGaussian.symm, lintegral_map hg (by fun_prop)]
    have hprod : ∀ x : Fin m → ℝ, g (WithLp.toLp 2 x) =
        ∏ i, ENNReal.ofReal (Real.exp (1 / 4 * x i ^ 2)) := by
      intro x
      simp only [g, EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
      rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
      congr 1; funext i; congr 2; simp; ring
    simp_rw [hprod]
    rw [lintegral_pi_prod (ι := Fin m) (gaussianReal 0 1)
      (f := fun z => ENNReal.ofReal (Real.exp (1 / 4 * z ^ 2))) (by fun_prop),
      lintegral_exp_mul_sq (by norm_num), Fintype.card_fin]
    norm_num
  have hmarkov : ENNReal.ofReal (Real.exp m) * μ {b | (m : ℝ) ≤ ‖b‖ ^ 2 / 4} ≤ ∫⁻ b, g b ∂μ := by
    refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hg.aemeasurable
      (ENNReal.ofReal (Real.exp m)))
    gcongr with b
    intro hb
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hb)
  have hs2 : Real.sqrt 2 ≤ Real.exp (1 / 2) := by
    refine Real.sqrt_le_iff.2 ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_nat_mul]
    have := Real.add_one_le_exp ((2 : ℕ) * (1 / 2 : ℝ))
    norm_num at this ⊢
    linarith
  calc outLaw m {a | 2 < ‖a‖}
      ≤ ENNReal.ofReal (Real.exp (-m)) * (ENNReal.ofReal (Real.exp m) *
          μ {b | (m : ℝ) ≤ ‖b‖ ^ 2 / 4}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        exact hset
    _ ≤ ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal (Real.sqrt 2) ^ m := by
        rw [← hint]; gcongr
    _ = ENNReal.ofReal (Real.exp (-(1 * m)) * Real.sqrt 2 ^ m) := by
        rw [one_mul, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (by positivity)]
    _ ≤ ENNReal.ofReal (rhoA m) := by
        refine ENNReal.ofReal_le_ofReal ((exp_pow_le (b := 1 / 2) (by positivity) ?_).trans_eq ?_)
        · calc Real.exp (-1) * Real.sqrt 2 ≤ Real.exp (-1) * Real.exp (1 / 2) := by gcongr
            _ = Real.exp (-(1 / 2)) := by rw [← Real.exp_add]; norm_num
        · rw [rhoA]; ring_nf

end GaussianSGD
