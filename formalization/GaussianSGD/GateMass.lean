import GaussianSGD.GateDefs
import GaussianSGD.Init

/-!
# Expected mass of the exceptional set in the fixed-gate regime (`thm:gate`)

For a fixed marginal, the set of cube points at which some gate might change has expected
mass at most `B_{n,m}(τ)` under the Gaussian initialization.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace GateMassAux

/-- `Pr(|Z| ≤ t) ≤ √(2/π) t` for `Z ∼ N(0,1)`. -/
lemma gaussianReal_abs_le (t : ℝ) :
    gaussianReal 0 1 {a | |a| ≤ t} ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * t) := by
  have hset : {a : ℝ | |a| ≤ t} = Set.Icc (-t) t := by ext a; simp [abs_le]
  have hpdf : ∀ a, gaussianPDF 0 1 a ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro a
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    have h1 : Real.exp (-a ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := sq_nonneg a; linarith)
    have h0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    nlinarith
  rw [gaussianReal_apply 0 one_ne_zero, hset]
  calc ∫⁻ a in Set.Icc (-t) t, gaussianPDF 0 1 a
      ≤ ∫⁻ _ in Set.Icc (-t) t, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ := lintegral_mono hpdf
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * ENNReal.ofReal (t - -t) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * t) := by
        rcases le_or_gt 0 t with ht | ht
        · rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
            Real.sqrt_mul (by norm_num) _
          have h3 : Real.sqrt (2 / Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi :=
            Real.sqrt_div' _ Real.pi_pos.le
          have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
          have hs2' : 0 < Real.sqrt 2 := by positivity
          rw [h2, h3]
          field_simp
          nlinarith
        · rw [ENNReal.ofReal_of_nonpos (by linarith : t - -t ≤ 0),
            ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) ht.le),
            mul_zero]

/-- `E|Z| = √(2/π)` for `Z ∼ N(0,1)`. -/
lemma integral_abs_gaussianReal : ∫ z, |z| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hcomp : ∀ z : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) * |z| =
      (fun t => (Real.sqrt (2 * Real.pi))⁻¹ * (t * Real.exp (-(1 / 2) * t ^ 2))) |z| := by
    intro z; simp only [sq_abs]; ring_nf
  have habs := integral_comp_abs
    (f := fun t => (Real.sqrt (2 * Real.pi))⁻¹ * (t * Real.exp (-(1 / 2) * t ^ 2)))
  simp_rw [hcomp]
  rw [habs, integral_const_mul]
  have hI : ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(1 / 2) * t ^ 2) = 1 := by
    have h := integral_mul_cexp_neg_mul_sq (b := ((1 / 2 : ℝ) : ℂ)) (by simp)
    have h' : ∫ t in Set.Ioi (0 : ℝ), ((t * Real.exp (-(1 / 2) * t ^ 2) : ℝ) : ℂ) = 1 := by
      rw [show (1 : ℂ) = (2 * ((1 / 2 : ℝ) : ℂ))⁻¹ by push_cast; norm_num, ← h]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring_nf
    rw [integral_complex_ofReal] at h'
    exact_mod_cast h'
  rw [hI, mul_one]
  have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  have h3 : Real.sqrt (2 / Real.pi) = Real.sqrt 2 / Real.sqrt Real.pi :=
    Real.sqrt_div' _ Real.pi_pos.le
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hs2' : 0 < Real.sqrt 2 := by positivity
  rw [h2, h3]
  field_simp
  nlinarith

/-- `E Z² = 1` for `Z ∼ N(0,1)`. -/
lemma integral_sq_gaussianReal : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- `E ‖ξ‖ ≤ √k` for a standard Gaussian vector `ξ` in `ℝ^k`. -/
lemma lintegral_sqrt_sum_sq_le (k : ℕ) :
    ∫⁻ w, ENNReal.ofReal (Real.sqrt (∑ j, w j ^ 2)) ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      ≤ ENNReal.ofReal (Real.sqrt k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk'
  have hint : ∀ j : Fin k, Integrable (fun w : Fin k → ℝ => w j ^ 2)
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := fun j =>
    integrable_comp_eval (μ := fun _ : Fin k => gaussianReal 0 1) (f := fun z : ℝ => z ^ 2)
      ((memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq)
  have hS : Integrable (fun w : Fin k → ℝ => ∑ j, w j ^ 2)
      (Measure.pi fun _ : Fin k => gaussianReal 0 1) := integrable_finsetSum _ fun j _ => hint j
  have hamgm : ∀ S : ℝ, 0 ≤ S → Real.sqrt S ≤ (S + k) / (2 * Real.sqrt k) := by
    intro S hS0
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt S - Real.sqrt k), Real.sq_sqrt hS0, Real.sq_sqrt hk'.le]
  calc ∫⁻ w, ENNReal.ofReal (Real.sqrt (∑ j, w j ^ 2)) ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      ≤ ∫⁻ w, ENNReal.ofReal ((∑ j, w j ^ 2 + k) / (2 * Real.sqrt k))
          ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) :=
        lintegral_mono fun w => ENNReal.ofReal_le_ofReal
          (hamgm _ (Finset.sum_nonneg fun j _ => sq_nonneg _))
    _ = ENNReal.ofReal (∫ w, (∑ j, w j ^ 2 + k) / (2 * Real.sqrt k)
          ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
        (ofReal_integral_eq_lintegral_ofReal ((hS.add (integrable_const _)).div_const _)
          (ae_of_all _ fun w => div_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)
            (Nat.cast_nonneg _)) (by positivity))).symm
    _ = ENNReal.ofReal (Real.sqrt k) := by
        congr 1
        rw [integral_div, integral_add hS (integrable_const _), integral_const,
          integral_finsetSum _ fun j _ => hint j]
        have hj : ∀ j : Fin k, ∫ w, w j ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = 1 :=
          fun j => by
            rw [integral_comp_eval (μ := fun _ : Fin k => gaussianReal 0 1) (f := fun z : ℝ => z ^ 2)
              (by fun_prop), integral_sq_gaussianReal]
        simp only [hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          probReal_univ, smul_eq_mul, one_mul]
        have := Real.mul_self_sqrt hk'.le
        field_simp
        linarith

/-- Standard Gaussian mass of the cone `{|⟪Z, e⟫| ≤ c + β ‖Z‖}` in `ℝ^{k+1}`. -/
lemma stdGaussian_cone_le {k : ℕ} (e : Vec (k + 1)) (he : ‖e‖ = 1) {c β : ℝ} (hc : 0 ≤ c)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    stdGaussian (Vec (k + 1)) {Z | |⟪Z, e⟫| ≤ c + β * ‖Z‖} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (c + β * Real.sqrt k) / (1 - β)) := by
  set Q : Vec (k + 1) ≃ₗᵢ[ℝ] Vec (k + 1) :=
    (ℝ ∙ (EuclideanSpace.single 0 1 - e))ᗮ.reflection
  have hQ : Q (EuclideanSpace.single 0 1) = e :=
    Submodule.reflection_sub (by simp [he])
  have hS : MeasurableSet {Z : Vec (k + 1) | |⟪Z, e⟫| ≤ c + β * ‖Z‖} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [← stdGaussian_map Q, Measure.map_apply (by fun_prop) hS]
  have hpre : ⇑Q ⁻¹' {Z | |⟪Z, e⟫| ≤ c + β * ‖Z‖} = {Y | |Y 0| ≤ c + β * ‖Y‖} := by
    ext Y
    simp [← hQ, LinearIsometryEquiv.inner_map_map, EuclideanSpace.inner_single_right]
  set γ : Measure ℝ := gaussianReal 0 1
  set ρ : (Fin k → ℝ) → ℝ := fun w => Real.sqrt (∑ j, w j ^ 2) with hρ
  set g : (Fin k → ℝ) → ℝ := fun w => (c + β * ρ w) / (1 - β) with hg
  have hY : MeasurableSet {Y : Vec (k + 1) | |Y 0| ≤ c + β * ‖Y‖} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [hpre, ← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) hY]
  have hsub : WithLp.toLp 2 ⁻¹' {Y : Vec (k + 1) | |Y 0| ≤ c + β * ‖Y‖} ⊆
      {ξ : Fin (k + 1) → ℝ | |ξ 0| ≤ g (fun j => ξ j.succ)} := by
    intro ξ hξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hξ ⊢
    have hnorm : ‖WithLp.toLp 2 ξ‖ ≤ |ξ 0| + ρ (fun j => ξ j.succ) := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs, hρ, Fin.sum_univ_succ]
      have hB : 0 ≤ ∑ j : Fin k, ξ j.succ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [Real.sq_sqrt hB, sq_abs (ξ 0), abs_nonneg (ξ 0), Real.sqrt_nonneg (∑ j : Fin k, ξ j.succ ^ 2)]
    simp only [hg]
    rw [le_div_iff₀ (by linarith)]
    have : |ξ 0| ≤ c + β * (|ξ 0| + ρ (fun j => ξ j.succ)) :=
      hξ.trans (by gcongr)
    nlinarith
  refine (measure_mono hsub).trans ?_
  have hρc : Continuous ρ := by simp only [hρ]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => γ) 0
  set A' : Set (ℝ × (Fin k → ℝ)) := {p | |p.1| ≤ g p.2}
  have hA' : MeasurableSet A' := measurableSet_le (by fun_prop) (hgc.comp continuous_snd).measurable
  have hpreA : {ξ : Fin (k + 1) → ℝ | |ξ 0| ≤ g (fun j => ξ j.succ)} = E ⁻¹' A' := by
    ext ξ
    simp only [E, A', MeasurableEquiv.piFinSuccAbove_apply, Set.mem_preimage, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [hpreA, hmp.measure_preimage hA'.nullMeasurableSet, Measure.prod_apply_symm hA']
  have hslice : ∀ w : Fin k → ℝ, γ ((fun a => (a, w)) ⁻¹' A') ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * g w) := fun w => gaussianReal_abs_le (g w)
  set K0 : ℝ := Real.sqrt (2 / Real.pi) * c / (1 - β)
  set K1 : ℝ := Real.sqrt (2 / Real.pi) * β / (1 - β)
  have hK0 : 0 ≤ K0 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hc) (by linarith)
  have hK1 : 0 ≤ K1 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hβ0) (by linarith)
  have hsplit : ∀ w, ENNReal.ofReal (Real.sqrt (2 / Real.pi) * g w) =
      ENNReal.ofReal K0 + ENNReal.ofReal K1 * ENNReal.ofReal (ρ w) := by
    intro w
    rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_add hK0 (mul_nonneg hK1 (Real.sqrt_nonneg _))]
    congr 1
    simp only [hg, hρ, K0, K1]
    field_simp
  calc ∫⁻ w, γ ((fun a => (a, w)) ⁻¹' A') ∂(Measure.pi fun _ : Fin k => γ)
      ≤ ∫⁻ w, (ENNReal.ofReal K0 + ENNReal.ofReal K1 * ENNReal.ofReal (ρ w))
          ∂(Measure.pi fun _ : Fin k => γ) :=
        lintegral_mono fun w => (hslice w).trans_eq (hsplit w)
    _ = ENNReal.ofReal K0 + ENNReal.ofReal K1 *
          ∫⁻ w, ENNReal.ofReal (ρ w) ∂(Measure.pi fun _ : Fin k => γ) := by
        rw [lintegral_add_left measurable_const,
          lintegral_const_mul _ hρc.measurable.ennreal_ofReal]
        simp
    _ ≤ ENNReal.ofReal K0 + ENNReal.ofReal K1 * ENNReal.ofReal (Real.sqrt k) := by
        gcongr
        exact lintegral_sqrt_sum_sq_le k
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (c + β * Real.sqrt k) / (1 - β)) := by
        rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_add hK0 (mul_nonneg hK1 (Real.sqrt_nonneg _))]
        congr 1
        simp only [K0, K1]
        field_simp

/-- The cone bound for a row `w ∼ N(0, I_n/n)` and a cube point. -/
lemma rowLaw_cone_le {n : ℕ} (hn : 1 ≤ n) (x : Cube n) {c β : ℝ} (hc : 0 ≤ c) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    rowLaw n {w | |⟪w, pt x⟫| ≤ c + β * (Real.sqrt n * ‖w‖)} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * (c + β * Real.sqrt (n - 1)) / (1 - β)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hsn : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  set e : Vec (k + 1) := (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ • pt x
  have he : ‖e‖ = 1 := by
    have h := InitAux.norm_pt_sq x
    have hpt : ‖pt x‖ = Real.sqrt ((k + 1 : ℕ) : ℝ) := by
      rw [← h, Real.sqrt_sq (norm_nonneg _)]
    rw [norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hsn, inv_mul_cancel₀ hsn.ne']
  have hS : MeasurableSet {w : Vec (k + 1) | |⟪w, pt x⟫| ≤ c + β * (Real.sqrt ((k + 1 : ℕ) : ℝ) * ‖w‖)} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [rowLaw, Measure.map_apply (by fun_prop) hS]
  have hpre : (fun v : Vec (k + 1) => (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ • v) ⁻¹'
      {w | |⟪w, pt x⟫| ≤ c + β * (Real.sqrt ((k + 1 : ℕ) : ℝ) * ‖w‖)} =
      {Z | |⟪Z, e⟫| ≤ c + β * ‖Z‖} := by
    ext Z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, e, real_inner_smul_left, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsn, mul_inv_cancel_left₀ hsn.ne']
  rw [hpre]
  refine (stdGaussian_cone_le e he hc hβ0 hβ1).trans_eq ?_
  have hk : ((k + 1 : ℕ) : ℝ) - 1 = k := by push_cast; ring
  rw [hk]

/-- `E|a₀ⱼ| = √(2/(πm))` for `a₀ ∼ N(0, I_m/m)`. -/
lemma lintegral_abs_outLaw {m : ℕ} (j : Fin m) :
    ∫⁻ a, ENNReal.ofReal |a j| ∂(outLaw m) =
      ENNReal.ofReal ((Real.sqrt m)⁻¹ * Real.sqrt (2 / Real.pi)) := by
  have habs : ∫⁻ t, ENNReal.ofReal |t| ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt (2 / Real.pi)) := by
    have hint : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => abs_nonneg t),
      integral_abs_gaussianReal]
  unfold outLaw
  rw [MeasureTheory.lintegral_map (by fun_prop) (by fun_prop), ← map_pi_eq_stdGaussian,
    MeasureTheory.lintegral_map (by fun_prop) (by fun_prop)]
  have hc : 0 ≤ (Real.sqrt m)⁻¹ := by positivity
  have h1 : ∀ X : Fin m → ℝ, ENNReal.ofReal |((Real.sqrt m)⁻¹ • WithLp.toLp 2 X) j| =
      ENNReal.ofReal (Real.sqrt m)⁻¹ * ENNReal.ofReal |X j| := by
    intro X
    rw [← ENNReal.ofReal_mul hc]
    simp [abs_mul, abs_of_nonneg hc]
  simp_rw [h1]
  rw [lintegral_const_mul _ (by fun_prop), ENNReal.ofReal_mul hc, ← habs]
  congr 1
  exact (measurePreserving_eval (μ := fun _ : Fin m => gaussianReal 0 1) j).lintegral_comp
    (f := fun t => ENNReal.ofReal |t|) (by fun_prop)

/-- `sinh τ ≤ 6τ/5` and `cosh τ - 1 ≤ 5τ²/9` for `0 ≤ τ ≤ 1`. -/
lemma sinh_cosh_le {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) :
    Real.sinh τ ≤ 6 / 5 * τ ∧ Real.cosh τ - 1 ≤ 5 / 9 * τ ^ 2 := by
  have h1 := Real.exp_bound (x := τ) (by rw [abs_of_nonneg hτ0]; exact hτ) (n := 5) (by norm_num)
  have h2 := Real.exp_bound (x := -τ) (by rw [abs_neg, abs_of_nonneg hτ0]; exact hτ) (n := 5)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
    abs_of_nonneg hτ0] at h1 h2
  norm_num at h1 h2
  rw [Real.sinh_eq, Real.cosh_eq]
  have ha := abs_le.mp h1
  have hb := abs_le.mp h2
  have hp2 : τ ^ 2 ≤ 1 := by nlinarith
  have hp3 : τ ^ 3 ≤ τ := by nlinarith
  have hp4 : τ ^ 4 ≤ τ ^ 2 := by nlinarith
  have hp5 : τ ^ 5 ≤ τ := by nlinarith [pow_le_one₀ hτ0 hτ (n := 4)]
  have hp5' : τ ^ 5 ≤ τ ^ 2 := by nlinarith [pow_le_one₀ hτ0 hτ (n := 3), sq_nonneg τ]
  constructor
  · nlinarith
  · nlinarith

end GateMassAux

open GateMassAux

/-- Fixed-gate regime (`thm:gate`), Gaussian estimate: `E_{W₀,a₀} D(𝔅) ≤ B_{n,m}(τ)` for every fixed marginal. -/
theorem gateSet_mass {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) (D : Dist n) :
    ∫⁻ W, ∫⁻ a, ENNReal.ofReal (∑ x, D.p x * (gateSet τ (W, a)).indicator 1 x)
        ∂(outLaw m) ∂(hiddenLaw n m) ≤ ENNReal.ofReal (gateBound n m τ) := by
  set s := Real.sinh τ with hs
  set b := Real.cosh τ - 1 with hb
  obtain ⟨-, hcosh⟩ := sinh_cosh_le hτ0 hτ
  have hs0 : 0 ≤ s := Real.sinh_nonneg_iff.mpr hτ0
  have hb0 : 0 ≤ b := by linarith [Real.one_le_cosh τ]
  have hb1 : b < 1 := by nlinarith
  have h1b : 0 < 1 - b := by linarith
  set E : Cube n → Fin m → Set (Params n m) := fun x j =>
    {θ | |⟪θ.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ j} with hE
  have hEm : ∀ x j, MeasurableSet (E x j) := by
    intro x j
    simp only [hE, gateRadius]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hind : ∀ (θ : Params n m) x,
      (gateSet τ θ).indicator (1 : Cube n → ℝ) x = (⋃ j, E x j).indicator 1 θ := by
    intro θ x
    by_cases h : ∃ j, |⟪θ.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ j
    · have h1 : x ∈ gateSet τ θ := h
      have h2 : θ ∈ ⋃ j, E x j := Set.mem_iUnion.2 h
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]; rfl
    · have h1 : x ∉ gateSet τ θ := h
      have h2 : θ ∉ ⋃ j, E x j := fun h' => h (Set.mem_iUnion.1 h')
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have hind01 : ∀ (θ : Params n m) x, 0 ≤ (gateSet τ θ).indicator (1 : Cube n → ℝ) x ∧
      (gateSet τ θ).indicator (1 : Cube n → ℝ) x ≤ 1 := by
    intro θ x
    by_cases h : x ∈ gateSet τ θ <;> simp [Set.indicator, h]
  set F : Params n m → ENNReal := fun θ =>
    ENNReal.ofReal (∑ x, D.p x * (gateSet τ θ).indicator 1 x) with hF
  have hFm : Measurable F := by
    have : F = fun θ => ENNReal.ofReal (∑ x, D.p x * (⋃ j, E x j).indicator 1 θ) := by
      funext θ; simp only [hF, hind]
    rw [this]
    refine Measurable.ennreal_ofReal (Finset.measurable_sum _ fun x _ => ?_)
    exact measurable_const.mul (measurable_one.indicator (MeasurableSet.iUnion (hEm x)))
  set μ : Measure (Params n m) := (hiddenLaw n m).prod (outLaw m) with hμ
  have hLHS : ∫⁻ W, ∫⁻ a, ENNReal.ofReal (∑ x, D.p x * (gateSet τ (W, a)).indicator 1 x)
      ∂(outLaw m) ∂(hiddenLaw n m) = ∫⁻ θ, F θ ∂μ :=
    (lintegral_prod F hFm.aemeasurable).symm
  rw [hLHS]
  have hle1 : ∫⁻ θ, F θ ∂μ ≤ 1 := by
    calc ∫⁻ θ, F θ ∂μ ≤ ∫⁻ _, 1 ∂μ := by
          refine lintegral_mono fun θ => ?_
          rw [← ENNReal.ofReal_one, ← D.sum_one]
          refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun x _ => ?_)
          have := hind01 θ x
          nlinarith [D.nonneg x]
      _ = 1 := by simp [hμ]
  set C1 : ℝ := Real.sqrt (2 / Real.pi) * Real.sqrt n * s / (1 - b)
  set C2 : ℝ := Real.sqrt (2 / Real.pi) * b * Real.sqrt (n - 1) / (1 - b)
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  set P : ℝ := C1 * ((Real.sqrt m)⁻¹ * Real.sqrt (2 / Real.pi)) + C2
  have hrow : ∀ x j, μ (E x j) ≤ ENNReal.ofReal P := by
    intro x j
    rw [hμ, Measure.prod_apply_symm (hEm x j)]
    calc ∫⁻ a, hiddenLaw n m ((fun W => (W, a)) ⁻¹' E x j) ∂(outLaw m)
        ≤ ∫⁻ a, (ENNReal.ofReal C1 * ENNReal.ofReal |a j| + ENNReal.ofReal C2) ∂(outLaw m) := by
          refine lintegral_mono fun a => ?_
          have hSm : MeasurableSet
              {w : Vec n | |⟪w, pt x⟫| ≤ Real.sqrt n * |a j| * s + b * (Real.sqrt n * ‖w‖)} :=
            measurableSet_le (by fun_prop) (by fun_prop)
          have hpre : (fun W => (W, a)) ⁻¹' E x j = Function.eval j ⁻¹'
              {w | |⟪w, pt x⟫| ≤ Real.sqrt n * |a j| * s + b * (Real.sqrt n * ‖w‖)} := by
            ext W
            simp only [hE, gateRadius, Set.mem_preimage, Set.mem_ofPred_eq, Function.eval]
            constructor <;> intro h <;> linarith
          rw [hpre, hiddenLaw,
            (measurePreserving_eval (μ := fun _ : Fin m => rowLaw n) j).measure_preimage
              hSm.nullMeasurableSet]
          refine (rowLaw_cone_le hn x (by positivity) hb0 hb1).trans ?_
          rw [← ENNReal.ofReal_mul hC1, ← ENNReal.ofReal_add (by positivity) hC2]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          simp only [C1, C2]
          ring
      _ = ENNReal.ofReal P := by
          rw [lintegral_add_left (by fun_prop), lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ (by fun_prop), lintegral_abs_outLaw, ← ENNReal.ofReal_mul hC1,
            ← ENNReal.ofReal_add (by positivity) hC2]
  have hmP : (m : ℝ) * P = (2 / Real.pi * Real.sqrt (n * m) * Real.sinh τ +
      Real.sqrt (2 / Real.pi) * m * Real.sqrt (n - 1) * (Real.cosh τ - 1)) /
        (2 - Real.cosh τ) := by
    have e2 : (2 : ℝ) - Real.cosh τ = 1 - b := by rw [hb]; ring
    have e3 : Real.sqrt (2 / Real.pi) * Real.sqrt (2 / Real.pi) = 2 / Real.pi :=
      Real.mul_self_sqrt (by positivity)
    have e4 : (m : ℝ) * (Real.sqrt m)⁻¹ = Real.sqrt m := by
      rw [← div_eq_mul_inv, Real.div_sqrt]
    have key : (m : ℝ) * P * (1 - b) = ((m : ℝ) * (Real.sqrt m)⁻¹) *
        (Real.sqrt (2 / Real.pi) * Real.sqrt (2 / Real.pi)) * Real.sqrt n * s +
        Real.sqrt (2 / Real.pi) * m * Real.sqrt (n - 1) * b := by
      simp only [P, C1, C2]
      field_simp
    rw [e3, e4] at key
    rw [e2, Real.sqrt_mul (Nat.cast_nonneg _), eq_div_iff h1b.ne', key, ← hs, ← hb]
    ring
  have hleX : ∫⁻ θ, F θ ∂μ ≤ ENNReal.ofReal ((m : ℝ) * P) := by
    have hpt : ∀ θ, F θ ≤ ∑ x, ENNReal.ofReal (D.p x) * ∑ j, (E x j).indicator 1 θ := by
      intro θ
      simp only [hF]
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (D.nonneg x) (hind01 θ x).1)]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [ENNReal.ofReal_mul (D.nonneg x)]
      gcongr
      rw [hind]
      by_cases h : θ ∈ ⋃ j, E x j
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
        rw [Set.indicator_of_mem h, Pi.one_apply, ENNReal.ofReal_one]
        have hj1 : (E x j).indicator (1 : Params n m → ENNReal) θ = 1 := by
          rw [Set.indicator_of_mem hj, Pi.one_apply]
        rw [← hj1]
        exact Finset.single_le_sum (f := fun i => (E x i).indicator (1 : Params n m → ENNReal) θ)
          (fun _ _ => bot_le) (Finset.mem_univ j)
      · rw [Set.indicator_of_notMem h]; simp
    have hmeas : ∀ x, Measurable fun θ => ∑ j, (E x j).indicator (1 : Params n m → ENNReal) θ :=
      fun x => Finset.measurable_sum _ fun j _ => measurable_one.indicator (hEm x j)
    calc ∫⁻ θ, F θ ∂μ
        ≤ ∫⁻ θ, ∑ x, ENNReal.ofReal (D.p x) * ∑ j, (E x j).indicator 1 θ ∂μ := lintegral_mono hpt
      _ = ∑ x, ENNReal.ofReal (D.p x) * ∑ j, μ (E x j) := by
          rw [lintegral_finsetSum _ fun x _ => (hmeas x).const_mul _]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [lintegral_const_mul _ (hmeas x),
            lintegral_finsetSum _ fun j _ => measurable_one.indicator (hEm x j)]
          simp_rw [lintegral_indicator_one (hEm x _)]
      _ ≤ ∑ x, ENNReal.ofReal (D.p x) * ∑ _j : Fin m, ENNReal.ofReal P := by
          gcongr with x _ j _
          exact hrow x j
      _ = ENNReal.ofReal ((m : ℝ) * P) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => D.nonneg x), D.sum_one,
            ENNReal.ofReal_one, one_mul, ENNReal.ofReal_mul (Nat.cast_nonneg m),
            ENNReal.ofReal_natCast]
  unfold gateBound
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one, ← hmP]
  exact le_min hle1 hleX

/-- Fixed-gate regime (`thm:gate`), the simplified bound `B_{n,m}(τ) ≤ 2√(nm) τ + m√n τ²` for `0 ≤ τ ≤ 1`. -/
theorem gateBound_le {n m : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) :
    gateBound n m τ ≤ 2 * Real.sqrt (n * m) * τ + m * Real.sqrt n * τ ^ 2 := by
  obtain ⟨hs, hc⟩ := sinh_cosh_le hτ0 hτ
  have hs0 : 0 ≤ Real.sinh τ := Real.sinh_nonneg_iff.mpr hτ0
  have hc0 : 0 ≤ Real.cosh τ - 1 := by linarith [Real.one_le_cosh τ]
  have hden : 4 / 9 ≤ 2 - Real.cosh τ := by nlinarith
  have hpi1 : 2 / Real.pi ≤ 2 / 3 := by
    gcongr; linarith [Real.pi_gt_three]
  have hpi2 : Real.sqrt (2 / Real.pi) ≤ 4 / 5 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d2]
  have hnm := Real.sqrt_nonneg ((n : ℝ) * m)
  have hn1 : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpi0 : 0 ≤ 2 / Real.pi := by positivity
  have hnum : 2 / Real.pi * Real.sqrt (n * m) * Real.sinh τ +
      Real.sqrt (2 / Real.pi) * m * Real.sqrt (n - 1) * (Real.cosh τ - 1) ≤
      4 / 9 * (2 * Real.sqrt (n * m) * τ + m * Real.sqrt n * τ ^ 2) := by
    have e1 : 2 / Real.pi * Real.sqrt (n * m) * Real.sinh τ ≤
        2 / 3 * Real.sqrt (n * m) * (6 / 5 * τ) := by
      gcongr
    have e2 : Real.sqrt (2 / Real.pi) * m * Real.sqrt (n - 1) * (Real.cosh τ - 1) ≤
        4 / 5 * m * Real.sqrt n * (5 / 9 * τ ^ 2) := by
      gcongr
    nlinarith [mul_nonneg hnm hτ0]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by linarith)]
  have hR : 0 ≤ 2 * Real.sqrt (n * m) * τ + m * Real.sqrt n * τ ^ 2 := by positivity
  nlinarith

end GaussianSGD
