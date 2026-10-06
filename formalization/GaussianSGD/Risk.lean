import GaussianSGD.Comparison
import GaussianSGD.SmallBall
import GaussianSGD.Kernel
import GaussianSGD.RiskLemmas

/-!
# Risk controlled by kernel correlation (`thm:risk`)

The conditional bound given a hidden layer in the good event, and the averaged
bound over the Gaussian initialization.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace RiskAux

/-- Pathwise step in the proof of `thm:risk`: when `‖a₀‖ ≤ 2` and `b₀ = √m a₀`, the conditional
error is at least the error of `sgn Z_D(·; b₀)` minus the disagreement bounds at the test
points. -/
theorem condErr_ge_of_norm_le {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (W : Fin m → Vec n) (hG : Good W)
    (h : Cube n → Bool) (D : Dist n) (b : Vec m) (ha : ‖(Real.sqrt m)⁻¹ • b‖ ≤ 2) :
    err D (fun x => sgn (Zsym (η * m) (psi W) D T x b)) h
      - ∑ x, D.p x * disBound (kappa n m + 3 * (η * m * T) / 8 * ‖mu (psi W) h D‖)
          (9 / 16 * (η * m * T) / Real.sqrt T) (Zsym (η * m) (psi W) D T x b)
      ≤ condErr η T (W, (Real.sqrt m)⁻¹ • b) h D := by
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hγ0 : 0 ≤ η * m := (mul_pos hη hm0).le
  have hψ : ∀ x, ‖psi W x‖ ^ 2 ≤ 9 / 16 := fun x => (hG x).2
  have hsm : Real.sqrt m • ((Real.sqrt m)⁻¹ • b) = b :=
    smul_inv_smul₀ (Real.sqrt_pos.2 hm0).ne' b
  set a := (Real.sqrt m)⁻¹ • b
  set S : Cube n → ℝ := fun x => sgn (Zsym (η * m) (psi W) D T x b)
  set d := kappa n m + 3 * (η * m * T) / 8 * ‖mu (psi W) h D‖ with hd
  set σ := 9 / 16 * (η * m * T) / Real.sqrt T with hσ
  set G : (Fin T → Cube n) → Cube n → ℝ :=
    fun s x => sgn (tailScore η T (W, a) (ext s) (labels h (ext s)) x)
  have key : ∀ x, ∑ s : Fin T → Cube n, histWeight D s * (if G s x = S x then 0 else 1)
      ≤ disBound d σ (Zsym (η * m) (psi W) D T x b) := by
    intro x
    refine sum_disagree_le Finset.univ (fun s => histWeight_nonneg D s) (sum_histWeight D)
      (E := fun s => ⟪tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b) -
          tailAvg T (fun t => (Pmap (η * m) (psi W) h D)^[t] b), psi W x⟫) ?_ ?_
    · intro s
      have h1 := tail_score_comparison hn hm hη hB hγ (W, a) hG ha (ext s) (labels h (ext s))
        (labels_pm h (ext s)) x
      simp only at h1
      rw [hsm] at h1
      have h2 := tail_label_effect hT hγ0 hγ (psi W) hψ h D b x
      unfold Zsym
      rw [inner_sub_left] at h2 ⊢
      calc |tailScore η T (W, a) (ext s) (labels h (ext s)) x -
            ⟪tailAvg T fun t => (Rmap (η * m) (psi W) D)^[t] b, psi W x⟫|
          = |(tailScore η T (W, a) (ext s) (labels h (ext s)) x -
              ⟪tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b), psi W x⟫)
            + (⟪tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b), psi W x⟫ -
              ⟪tailAvg T fun t => (Pmap (η * m) (psi W) h D)^[t] b, psi W x⟫)
            + (⟪tailAvg T fun t => (Pmap (η * m) (psi W) h D)^[t] b, psi W x⟫ -
              ⟪tailAvg T fun t => (Rmap (η * m) (psi W) D)^[t] b, psi W x⟫)| := by
            congr 1; ring
        _ ≤ _ := by
            refine (abs_add_three _ _ _).trans ?_
            rw [hd]; linarith
    · have h3 := tail_sq_error hT hγ0 hγ (psi W) hψ h D b
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      calc ∑ s : Fin T → Cube n, histWeight D s *
            ⟪tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b) -
              tailAvg T (fun t => (Pmap (η * m) (psi W) h D)^[t] b), psi W x⟫ ^ 2
          ≤ ∑ s : Fin T → Cube n, histWeight D s *
            (‖tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b) -
              tailAvg T (fun t => (Pmap (η * m) (psi W) h D)^[t] b)‖ ^ 2 * (9 / 16)) := by
            refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (histWeight_nonneg D s)
            rw [← sq_abs]
            refine (pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2).trans ?_
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (hψ x) (by positivity)
        _ = (∑ s : Fin T → Cube n, histWeight D s *
            ‖tailAvg T (frozen (η * m) (psi W) (ext s) (labels h (ext s)) b) -
              tailAvg T (fun t => (Pmap (η * m) (psi W) h D)^[t] b)‖ ^ 2) * (9 / 16) := by
            rw [Finset.sum_mul]; congr 1; ext s; ring
        _ ≤ 9 / 16 * (η * m * T) ^ 2 / T * (9 / 16) := by gcongr
        _ = σ ^ 2 := by
            rw [hσ, div_pow, Real.sq_sqrt hTpos.le]; ring
  calc err D S h - ∑ x, D.p x * disBound d σ (Zsym (η * m) (psi W) D T x b)
      ≤ err D S h - ∑ x, D.p x *
          ∑ s : Fin T → Cube n, histWeight D s * (if G s x = S x then 0 else 1) := by
        gcongr with x
        · exact D.nonneg x
        · exact key x
    _ = ∑ s : Fin T → Cube n, histWeight D s *
          (err D S h - ∑ x, D.p x * (if G s x = S x then 0 else 1)) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_histWeight, one_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1; refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ∑ s : Fin T → Cube n, histWeight D s * err D (G s) h := by
        refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (histWeight_nonneg D s)
        exact err_ge D (G s) S h
    _ = condErr η T (W, a) h D := rfl

/-- `E_{W₀} ‖μ‖ ≤ A_D(h)`, by Jensen's inequality and `E_{W₀} ‖μ‖² = A_D(h)²`. -/
lemma integral_norm_mu_le {n m : ℕ} (hm : 1 ≤ m) (h : Cube n → Bool)
    (D : Dist n) : ∫ W, ‖mu (psi W) h D‖ ∂(hiddenLaw n m) ≤ kernelCorr h D := by
  have hX : MemLp (fun W => ‖mu (psi W) h D‖) 2 (hiddenLaw n m) :=
    (memLp_two_iff_integrable_sq (integrable_norm_mu h D).aestronglyMeasurable).2
      (integrable_norm_mu_sq h D)
  have h1 := variance_nonneg (fun W => ‖mu (psi W) h D‖) (hiddenLaw n m)
  rw [variance_eq_sub hX] at h1
  have h2 : ∫ W, ((fun W => ‖mu (psi W) h D‖) ^ 2) W ∂(hiddenLaw n m) = kernelCorr h D ^ 2 :=
    kernel_identity hm h D
  refine le_of_pow_le_pow_left₀ two_ne_zero (Real.sqrt_nonneg _) ?_
  rw [← h2]; linarith

end RiskAux

/-- Risk controlled by kernel correlation (`thm:risk`), conditional on a hidden layer
in the good event. -/
theorem cond_risk_lower {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (W : Fin m → Vec n) (hG : Good W)
    (h : Cube n → Bool) (D : Dist n) :
    ENNReal.ofReal (1 / 2 - rhoA m - 24 * kappa n m - 27 * (η * m * T) / Real.sqrt T
        - 9 * (η * m * T) * ‖mu (psi W) h D‖)
      ≤ ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hγ0 : 0 < η * m := mul_pos hη hmR
  set d := kappa n m + 3 * (η * m * T) / 8 * ‖mu (psi W) h D‖ with hd
  set σ := 9 / 16 * (η * m * T) / Real.sqrt T with hσ
  have hd0 : 0 ≤ d := by rw [hd]; unfold kappa; positivity
  have hσ0 : 0 ≤ σ := by positivity
  set Z : Cube n → Vec m → ℝ := fun x b => Zsym (η * m) (psi W) D T x b with hZ
  have hZm : ∀ x, Measurable (Z x) := fun x => (continuous_Zsym _ _ _ _ x).measurable
  set bad : Set (Vec m) := {b | 2 < ‖(Real.sqrt m)⁻¹ • b‖} with hbad_def
  have hbad : MeasurableSet bad :=
    measurableSet_lt measurable_const (measurable_const_smul _).norm
  set L : Vec m → ℝ := fun b => err D (fun x => sgn (Z x b)) h
    - ∑ x, D.p x * RiskAux.disBound d σ (Z x b) - bad.indicator 1 b with hL
  have hsum0 : ∀ b, 0 ≤ ∑ x, D.p x * RiskAux.disBound d σ (Z x b) := fun b =>
    Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (RiskAux.disBound_nonneg _ _ _)
  have hpt : ∀ b, L b ≤ condErr η T (W, (Real.sqrt m)⁻¹ • b) h D := by
    intro b
    by_cases hb : b ∈ bad
    · have h1 : L b ≤ 0 := by
        simp only [hL, Set.indicator_of_mem hb, Pi.one_apply]
        linarith [RiskAux.err_le_one D (fun x => sgn (Z x b)) h, hsum0 b]
      exact h1.trans (RiskAux.condErr_nonneg _ _ _ _ _)
    · simp only [hL, Set.indicator_of_notMem hb, sub_zero]
      exact RiskAux.condErr_ge_of_norm_le hn hm hT hη hB hγ W hG h D b (not_lt.1 hb)
  have hint1 : Integrable (fun b => err D (fun x => sgn (Z x b)) h) (stdGaussian (Vec m)) := by
    refine Integrable.of_bound (RiskAux.measurable_err_comp D h hZm).aestronglyMeasurable 1
      (ae_of_all _ fun b => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (err_nonneg _ _ _)]
    exact RiskAux.err_le_one _ _ _
  have hint2 : ∀ x, Integrable (fun b => RiskAux.disBound d σ (Z x b)) (stdGaussian (Vec m)) := by
    intro x
    refine Integrable.of_bound
      ((RiskAux.measurable_disBound d σ).comp (hZm x)).aestronglyMeasurable 1
      (ae_of_all _ fun b => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (RiskAux.disBound_nonneg _ _ _)]
    exact RiskAux.disBound_le_one _ _ _
  have hint3 : Integrable (bad.indicator (1 : Vec m → ℝ)) (stdGaussian (Vec m)) :=
    (integrable_const (1 : ℝ)).indicator hbad
  have hint23 :
      Integrable (fun b => ∑ x, D.p x * RiskAux.disBound d σ (Z x b)) (stdGaussian (Vec m)) :=
    integrable_finsetSum _ fun x _ => (hint2 x).const_mul _
  have hint12 : Integrable (fun b => err D (fun x => sgn (Z x b)) h
      - ∑ x, D.p x * RiskAux.disBound d σ (Z x b)) (stdGaussian (Vec m)) := hint1.sub hint23
  have hint : Integrable L (stdGaussian (Vec m)) := hint12.sub hint3
  have hLint : ∫ b, L b ∂(stdGaussian (Vec m)) = 1 / 2
      - ∑ x, D.p x * ∫ b, RiskAux.disBound d σ (Z x b) ∂(stdGaussian (Vec m))
      - (stdGaussian (Vec m)).real bad := by
    change ∫ b, (err D (fun x => sgn (Z x b)) h - ∑ x, D.p x * RiskAux.disBound d σ (Z x b)
      - bad.indicator 1 b) ∂(stdGaussian (Vec m)) = _
    rw [integral_sub hint12 hint3, integral_sub hint1 hint23,
      integral_finsetSum _ fun x _ => (hint2 x).const_mul _, integral_indicator_one hbad]
    simp only [hZ, integral_const_mul]
    rw [null_risk hγ0 hγ hB (psi W) hG D h]
  have hdis : ∀ x,
      ∫ b, RiskAux.disBound d σ (Z x b) ∂(stdGaussian (Vec m)) ≤ 24 * d + 2 * (24 * σ) :=
    fun x => RiskAux.integral_disBound_le _ (hZm x) (by norm_num) hd0 hσ0
      (fun r hr => smallball hγ0 hγ hB (psi W) hG D x hr)
  have hbadle : (stdGaussian (Vec m)).real bad ≤ rhoA m := by
    rw [Measure.real, hbad_def, RiskAux.stdGaussian_norm_gt]
    exact ENNReal.toReal_le_of_le_ofReal (by unfold rhoA; positivity) (init_output m)
  have hsum : ∑ x, D.p x * ∫ b, RiskAux.disBound d σ (Z x b) ∂(stdGaussian (Vec m))
      ≤ 24 * d + 2 * (24 * σ) := by
    calc ∑ x, D.p x * ∫ b, RiskAux.disBound d σ (Z x b) ∂(stdGaussian (Vec m))
        ≤ ∑ x, D.p x * (24 * d + 2 * (24 * σ)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hdis x) (D.nonneg x)
      _ = 24 * d + 2 * (24 * σ) := by rw [← Finset.sum_mul, D.sum_one, one_mul]
  calc ENNReal.ofReal (1 / 2 - rhoA m - 24 * kappa n m - 27 * (η * m * T) / Real.sqrt T
        - 9 * (η * m * T) * ‖mu (psi W) h D‖)
      = ENNReal.ofReal (1 / 2 - (24 * d + 2 * (24 * σ)) - rhoA m) := by
        congr 1; rw [hd, hσ]; ring
    _ ≤ ENNReal.ofReal (∫ b, L b ∂(stdGaussian (Vec m))) :=
        ENNReal.ofReal_le_ofReal (by rw [hLint]; linarith)
    _ ≤ ∫⁻ b, ENNReal.ofReal (L b) ∂(stdGaussian (Vec m)) :=
        RiskAux.ofReal_integral_le_lintegral_ofReal hint
    _ ≤ ∫⁻ b, ENNReal.ofReal (condErr η T (W, (Real.sqrt m)⁻¹ • b) h D)
          ∂(stdGaussian (Vec m)) :=
        lintegral_mono fun b => ENNReal.ofReal_le_ofReal (hpt b)
    _ = ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) :=
        (RiskAux.lintegral_outLaw hm0 (fun a => ENNReal.ofReal (condErr η T (W, a) h D))).symm

/-- Risk controlled by kernel correlation (`thm:risk`). -/
theorem risk_lower_bound {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (h : Cube n → Bool) (D : Dist n) :
    ENNReal.ofReal (1 / 2 - lossTerm n m T (η * m * T) - 9 * (η * m * T) * kernelCorr h D)
      ≤ risk m η T h D := by
  have hm1 : 1 ≤ m := by omega
  have hBnn : 0 ≤ η * m * T := by positivity
  set r := rhoA m + 24 * kappa n m + 27 * (η * m * T) / Real.sqrt T with hr_def
  have hr : 0 ≤ r := by rw [hr_def]; unfold rhoA kappa; positivity
  set G := {W : Fin m → Vec n | Good W}
  have hGm : MeasurableSet G := RiskAux.measurableSet_good n m
  set f : (Fin m → Vec n) → ℝ := G.indicator (fun W => 1 / 2 - rhoA m - 24 * kappa n m
    - 27 * (η * m * T) / Real.sqrt T - 9 * (η * m * T) * ‖mu (psi W) h D‖) with hf_def
  have hpt : ∀ W,
      ENNReal.ofReal (f W) ≤ ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) := by
    intro W
    by_cases hW : W ∈ G
    · rw [hf_def, Set.indicator_of_mem hW]
      exact cond_risk_lower hn hm hT hη hB hγ W hW h D
    · rw [hf_def, Set.indicator_of_notMem hW, ENNReal.ofReal_zero]
      positivity
  have hmu := integrable_norm_mu (m := m) h D
  have hint : Integrable f (hiddenLaw n m) :=
    ((integrable_const _).sub (hmu.const_mul (9 * (η * m * T)))).indicator hGm
  have hfint : ∫ W, f W ∂(hiddenLaw n m) = (1 / 2 - r) * (hiddenLaw n m).real G
      - 9 * (η * m * T) * ∫ W in G, ‖mu (psi W) h D‖ ∂(hiddenLaw n m) := by
    rw [hf_def, integral_indicator hGm, integral_sub (integrable_const _).integrableOn
      (hmu.const_mul _).integrableOn, setIntegral_const, integral_const_mul, smul_eq_mul, hr_def]
    ring
  have hPG : 1 - rhoW n m ≤ (hiddenLaw n m).real G := by
    have h1 : (hiddenLaw n m).real Gᶜ ≤ rhoW n m :=
      ENNReal.toReal_le_of_le_ofReal (by unfold rhoW; positivity) (init_hidden hn)
    rw [probReal_compl_eq_one_sub hGm] at h1
    linarith
  have hPG1 : (hiddenLaw n m).real G ≤ 1 := measureReal_le_one
  have hmuG : ∫ W in G, ‖mu (psi W) h D‖ ∂(hiddenLaw n m) ≤ kernelCorr h D :=
    (setIntegral_le_integral hmu (ae_of_all _ fun W => norm_nonneg _)).trans
      (RiskAux.integral_norm_mu_le hm1 h D)
  calc ENNReal.ofReal (1 / 2 - lossTerm n m T (η * m * T) - 9 * (η * m * T) * kernelCorr h D)
      ≤ ENNReal.ofReal (∫ W, f W ∂(hiddenLaw n m)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hfint]
        unfold lossTerm
        have h1 : r * (hiddenLaw n m).real G ≤ r := mul_le_of_le_one_right hr hPG1
        have h2 := mul_le_mul_of_nonneg_left hmuG (by positivity : (0 : ℝ) ≤ 9 * (η * m * T))
        rw [hr_def] at h1
        nlinarith
    _ ≤ ∫⁻ W, ENNReal.ofReal (f W) ∂(hiddenLaw n m) :=
        RiskAux.ofReal_integral_le_lintegral_ofReal hint
    _ ≤ risk m η T h D := lintegral_mono hpt

end GaussianSGD
