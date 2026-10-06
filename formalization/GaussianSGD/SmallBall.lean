import GaussianSGD.Density
import GaussianSGD.Population

/-!
# Anti-concentration of the symmetric tail (`lem:smallball`)

For every cube point the symmetric tail score has small-ball probability at most
`24 r` under the standard Gaussian initialization, and its sign has expected
error exactly `1/2` against every Boolean target.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace SmallBall

/-- The symmetric tail score as a function of the state at the start of the tail. -/
def Ztail {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ) (x : Cube n)
    (v : Vec m) : ℝ :=
  ⟪((tail T).card : ℝ)⁻¹ • ∑ t ∈ tail T, (Rmap γ ψ D)^[t - (T + 1) / 2] v, ψ x⟫

theorem continuous_Ztail {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ)
    (x : Cube n) : Continuous (Ztail γ ψ D T x) := by
  have := fun t : ℕ => (continuous_Rmap γ ψ D).iterate t
  unfold Ztail
  fun_prop

theorem Zsym_eq_Ztail {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ)
    (x : Cube n) (b : Vec m) :
    Zsym γ ψ D T x b = Ztail γ ψ D T x ((Rmap γ ψ D)^[(T + 1) / 2] b) := by
  unfold Zsym Ztail tailAvg
  congr 2
  refine Finset.sum_congr rfl fun t ht => ?_
  have hst : (T + 1) / 2 ≤ t := (Finset.mem_Icc.mp ht).1
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hst]

/-- For `δ_j = R^j(v) - R^j(w)`, `‖δ_j‖ ≤ ‖δ_0‖` and `‖δ_j - δ_0‖ ≤ j (9γ/64) ‖δ_0‖`. -/
theorem iterate_dev {n m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (ψ : Cube n → Vec m)
    (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (v w : Vec m) (j : ℕ) :
    ‖(Rmap γ ψ D)^[j] v - (Rmap γ ψ D)^[j] w‖ ≤ ‖v - w‖ ∧
      ‖((Rmap γ ψ D)^[j] v - (Rmap γ ψ D)^[j] w) - (v - w)‖ ≤ j * (9 * γ / 64) * ‖v - w‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    set a := (Rmap γ ψ D)^[j] v
    set b := (Rmap γ ψ D)^[j] w
    refine ⟨(Rmap_nonexpansive hγ0 hγ ψ hψ D a b).trans ih.1, ?_⟩
    have h1 := Population.Rmap_sub_sub_le hγ0 ψ hψ D a b
    have he : (Rmap γ ψ D a - Rmap γ ψ D b) - (v - w) =
        ((Rmap γ ψ D a - Rmap γ ψ D b) - (a - b)) + ((a - b) - (v - w)) := by abel
    rw [he]
    have hγ' : 0 ≤ 9 * γ / 64 := by positivity
    calc _ ≤ ‖(Rmap γ ψ D a - Rmap γ ψ D b) - (a - b)‖ + ‖(a - b) - (v - w)‖ := norm_add_le _ _
      _ ≤ 9 * γ / 64 * ‖a - b‖ + j * (9 * γ / 64) * ‖v - w‖ := add_le_add h1 ih.2
      _ ≤ 9 * γ / 64 * ‖v - w‖ + j * (9 * γ / 64) * ‖v - w‖ := by
          gcongr; exact ih.1
      _ = ((j + 1 : ℕ) : ℝ) * (9 * γ / 64) * ‖v - w‖ := by push_cast; ring

/-- Secant form of the derivative bound `eq:derivative` in the proof of `lem:smallball`: along
the direction of `ψ(x)` the tail score increases at rate at least `(5/32) ‖ψ(x)‖`. -/
theorem Ztail_mono {n m T : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (hB : γ * T ≤ 12)
    (ψ : Cube n → Vec m) (hψ : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (x : Cube n)
    (hx : ψ x ≠ 0) (v : Vec m) {a a' : ℝ} (haa : a ≤ a') :
    5 / 32 * ‖ψ x‖ * (a' - a) ≤
      Ztail γ ψ D T x (v + a' • (‖ψ x‖⁻¹ • ψ x)) - Ztail γ ψ D T x (v + a • (‖ψ x‖⁻¹ • ψ x)) := by
  set e := ‖ψ x‖⁻¹ • ψ x with he_def
  set s := (T + 1) / 2
  have hnx : 0 < ‖ψ x‖ := norm_pos_iff.mpr hx
  have hne : (tail T).Nonempty := ⟨T, by
    simp only [tail, Finset.mem_Icc, le_refl, and_true]; omega⟩
  have hc : (0 : ℝ) < (tail T).card := by exact_mod_cast hne.card_pos
  have hδ0 : (v + a' • e) - (v + a • e) = (a' - a) • e := by
    rw [add_sub_add_left_eq_sub, sub_smul]
  have hnδ0 : ‖(v + a' • e) - (v + a • e)‖ = a' - a := by
    rw [hδ0, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr haa), he_def, norm_smul, norm_inv,
      norm_norm, inv_mul_cancel₀ hnx.ne', mul_one]
  have hinδ0 : ⟪(v + a' • e) - (v + a • e), ψ x⟫ = (a' - a) * ‖ψ x‖ := by
    rw [hδ0, he_def, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hterm : ∀ t ∈ tail T, 5 / 32 * ‖ψ x‖ * (a' - a) ≤
      ⟪(Rmap γ ψ D)^[t - s] (v + a' • e) - (Rmap γ ψ D)^[t - s] (v + a • e), ψ x⟫ := by
    intro t ht
    have htT := Finset.mem_Icc.mp ht
    have hj : (2 * (t - s) : ℕ) ≤ T := by omega
    have hjγ : ((t - s : ℕ) : ℝ) * γ ≤ 6 := by
      have : ((2 * (t - s) : ℕ) : ℝ) ≤ T := by exact_mod_cast hj
      push_cast at this
      nlinarith
    obtain ⟨-, h2⟩ := iterate_dev hγ0 hγ ψ hψ D (v + a' • e) (v + a • e) (t - s)
    rw [hnδ0] at h2
    set δ := (Rmap γ ψ D)^[t - s] (v + a' • e) - (Rmap γ ψ D)^[t - s] (v + a • e)
    have hsplit : ⟪δ, ψ x⟫ = ⟪(v + a' • e) - (v + a • e), ψ x⟫ +
        ⟪δ - ((v + a' • e) - (v + a • e)), ψ x⟫ := by
      rw [← inner_add_left, add_sub_cancel]
    have hlow : -(((t - s : ℕ) : ℝ) * (9 * γ / 64) * (a' - a)) * ‖ψ x‖ ≤
        ⟪δ - ((v + a' • e) - (v + a • e)), ψ x⟫ := by
      have := (abs_le.mp ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg (ψ x))))).1
      linarith
    rw [hsplit, hinδ0]
    have haa' : 0 ≤ a' - a := sub_nonneg.mpr haa
    have : ((t - s : ℕ) : ℝ) * (9 * γ / 64) * (a' - a) * ‖ψ x‖ ≤
        27 / 32 * (a' - a) * ‖ψ x‖ := by
      have h3 : ((t - s : ℕ) : ℝ) * (9 * γ / 64) ≤ 27 / 32 := by nlinarith
      have := mul_le_mul_of_nonneg_right h3 haa'
      exact mul_le_mul_of_nonneg_right this hnx.le
    nlinarith
  unfold Ztail
  rw [← inner_sub_left, ← smul_sub, ← Finset.sum_sub_distrib, real_inner_smul_left,
    sum_inner]
  calc 5 / 32 * ‖ψ x‖ * (a' - a)
      = ((tail T).card : ℝ)⁻¹ * ∑ _t ∈ tail T, 5 / 32 * ‖ψ x‖ * (a' - a) := by
        rw [Finset.sum_const, nsmul_eq_mul]; field_simp
    _ ≤ _ := by
        gcongr with t ht
        exact hterm t ht

/-- Small-ball bound for a one-dimensional standard Gaussian pulled back through a map whose
secant slopes are at least `c`. -/
theorem gaussianReal_smallball (φ : ℝ → ℝ) {c r : ℝ} (hc : 0 < c)
    (hφ : ∀ a a', a ≤ a' → c * (a' - a) ≤ φ a' - φ a) :
    gaussianReal 0 1 {a | |φ a| ≤ r} ≤
      ENNReal.ofReal ((√(2 * Real.pi))⁻¹ * (2 * r / c)) := by
  have hpdf : ∀ a, gaussianPDF 0 1 a ≤ ENNReal.ofReal ((√(2 * Real.pi))⁻¹) := by
    intro a
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    have h1 : Real.exp (-a ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := sq_nonneg a; linarith)
    have h0 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
    calc (√(2 * Real.pi))⁻¹ * Real.exp (-a ^ 2 / 2) ≤ (√(2 * Real.pi))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  have hdiam : volume {a | |φ a| ≤ r} ≤ ENNReal.ofReal (2 * r / c) := by
    refine (Real.volume_le_diam _).trans (Metric.ediam_le fun a ha a' ha' => ?_)
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : ∀ p q, |φ p| ≤ r → |φ q| ≤ r → p ≤ q → q - p ≤ 2 * r / c := by
      intro p q hp hq hpq
      have h1 := hφ p q hpq
      rw [le_div_iff₀ hc]
      have := abs_le.mp hp; have := abs_le.mp hq
      nlinarith
    rcases le_total a a' with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]; exact key a a' ha ha' h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact key a' a ha' ha h
  rw [gaussianReal_apply 0 one_ne_zero]
  calc ∫⁻ a in {a | |φ a| ≤ r}, gaussianPDF 0 1 a
      ≤ ∫⁻ a in {a | |φ a| ≤ r}, ENNReal.ofReal ((√(2 * Real.pi))⁻¹) := lintegral_mono hpdf
    _ = ENNReal.ofReal ((√(2 * Real.pi))⁻¹) * volume {a | |φ a| ≤ r} := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((√(2 * Real.pi))⁻¹) * ENNReal.ofReal (2 * r / c) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- If every line in the direction of a unit vector `e` meets `S` in a set of standard Gaussian
mass at most `ℓ`, then `S` has standard Gaussian mass at most `ℓ`. -/
theorem stdGaussian_le_of_slices {m : ℕ} (e : Vec m) (he : ‖e‖ = 1) {S : Set (Vec m)}
    (hS : MeasurableSet S) {ℓ : ENNReal}
    (hsl : ∀ v : Vec m, gaussianReal 0 1 {a | v + a • e ∈ S} ≤ ℓ) :
    stdGaussian (Vec m) S ≤ ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · exfalso
      have : e = 0 := Subsingleton.elim _ _
      rw [this, norm_zero] at he
      exact zero_ne_one he
    · exact ⟨k, rfl⟩
  set Q : Vec (k + 1) ≃ₗᵢ[ℝ] Vec (k + 1) :=
    (ℝ ∙ (EuclideanSpace.single 0 1 - e))ᗮ.reflection
  have hQ : Q (EuclideanSpace.single 0 1) = e :=
    Submodule.reflection_sub (by simp [he])
  set b := (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).map Q
  have hb0 : b 0 = e := by simp [b, hQ]
  set f : (Fin (k + 1) → ℝ) → Vec (k + 1) := fun x => ∑ i, x i • b i
  have hf : Measurable f := by fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_apply hf hS]
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0).symm
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0
  have hA : MeasurableSet (E.symm ⁻¹' (f ⁻¹' S)) := E.symm.measurable (hf hS)
  rw [← hmp.measure_preimage (hf hS).nullMeasurableSet, Measure.prod_apply_symm hA]
  calc _ ≤ ∫⁻ _, ℓ ∂(Measure.pi fun j : Fin k => gaussianReal 0 1) := lintegral_mono fun w => ?_
    _ = ℓ := by rw [lintegral_const, measure_univ, mul_one]
  have hslice : (fun a => (a, w)) ⁻¹' (E.symm ⁻¹' (f ⁻¹' S)) =
      {a | (∑ j, w j • b (Fin.succ j)) + a • e ∈ S} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, f, E, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.insertNthEquiv_apply, Fin.insertNth_zero', Fin.cons_zero, Fin.cons_succ, hb0]
    rw [add_comm (a • e)]
  rw [hslice]
  exact hsl _

/-- Started from `-b`, the symmetric recurrence is the negation of the one started from `b`. -/
theorem iterate_Rmap_neg {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (t : ℕ)
    (b : Vec m) : (Rmap γ ψ D)^[t] (-b) = -(Rmap γ ψ D)^[t] b := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Rmap_neg]

theorem Zsym_neg {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ) (x : Cube n)
    (b : Vec m) : Zsym γ ψ D T x (-b) = -Zsym γ ψ D T x b := by
  simp only [Zsym, tailAvg, iterate_Rmap_neg, Finset.sum_neg_distrib, smul_neg, inner_neg_left]

theorem sgn_ne_one (z : ℝ) : sgn z ≠ 1 ↔ z < 0 := by
  unfold sgn
  split_ifs with hz
  · simp only [ne_eq, not_true_eq_false, false_iff, not_lt]; exact hz
  · simp only [not_le] at hz; simp only [hz, iff_true]; norm_num

theorem sgn_ne_neg_one (z : ℝ) : sgn z ≠ -1 ↔ ¬z < 0 := by
  unfold sgn
  split_ifs with hz
  · simp only [not_lt, hz, iff_true]; norm_num
  · simp only [not_le] at hz; simp [hz]

end SmallBall

open SmallBall

/-- Anti-concentration of the symmetric tail (`lem:smallball`), small-ball bound. -/
theorem smallball {n m T : ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m)
    (hψ : ∀ x, 7 / 16 ≤ ‖ψ x‖ ^ 2 ∧ ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (x : Cube n)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Vec m) {b | |Zsym γ ψ D T x b| ≤ r} ≤ ENNReal.ofReal (24 * r) := by
  have hψ' : ∀ x, ‖ψ x‖ ^ 2 ≤ 9 / 16 := fun x => (hψ x).2
  have hnx : 0 < ‖ψ x‖ := by
    have := (hψ x).1
    by_contra hle
    have h0 : ‖ψ x‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [h0] at this
    norm_num at this
  have hx : ψ x ≠ 0 := norm_pos_iff.mp hnx
  set e := ‖ψ x‖⁻¹ • ψ x with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  set c := 5 / 32 * ‖ψ x‖ with hc_def
  have hc : 0 < c := by positivity
  set S := {v : Vec m | |Ztail γ ψ D T x v| ≤ r} with hS_def
  have hS : MeasurableSet S :=
    (isClosed_le (continuous_Ztail γ ψ D T x).abs continuous_const).measurableSet
  have hcπ : 1 / 4 ≤ c * √(2 * Real.pi) := by
    have hπ := Real.pi_gt_three
    have h2 : (c * √(2 * Real.pi)) ^ 2 = c ^ 2 * (2 * Real.pi) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h3 : (1 / 4 : ℝ) ^ 2 ≤ (c * √(2 * Real.pi)) ^ 2 := by
      rw [h2, hc_def, mul_pow]
      have := (hψ x).1
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (by positivity) two_ne_zero).mp h3
  have hG : stdGaussian (Vec m) S ≤ ENNReal.ofReal (8 * r) := by
    refine stdGaussian_le_of_slices e he hS fun v => ?_
    refine (gaussianReal_smallball (fun a => Ztail γ ψ D T x (v + a • e)) hc
      fun a a' haa => Ztail_mono hγ0.le hγ hB ψ hψ' D x hx v haa).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : 0 < √(2 * Real.pi) := by positivity
    rw [inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hR : Measurable ((Rmap γ ψ D)^[(T + 1) / 2]) :=
    ((continuous_Rmap γ ψ D).iterate _).measurable
  have hset : {b | |Zsym γ ψ D T x b| ≤ r} = (Rmap γ ψ D)^[(T + 1) / 2] ⁻¹' S := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS_def, Zsym_eq_Ztail]
  rw [hset, ← Measure.map_apply hR hS]
  have hdens := density_bound hγ0 hγ hB ψ hψ' D
  calc (stdGaussian (Vec m)).map ((Rmap γ ψ D)^[(T + 1) / 2]) S
      ≤ (ENNReal.ofReal (Real.exp 1) • stdGaussian (Vec m)) S := Measure.le_iff'.mp hdens S
    _ = ENNReal.ofReal (Real.exp 1) * stdGaussian (Vec m) S := by
        rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (8 * r) := by gcongr
    _ = ENNReal.ofReal (Real.exp 1 * (8 * r)) := (ENNReal.ofReal_mul (Real.exp_pos 1).le).symm
    _ ≤ ENNReal.ofReal (24 * r) :=
        ENNReal.ofReal_le_ofReal (by have := Real.exp_one_lt_d9; nlinarith)

/-- Anti-concentration of the symmetric tail (`lem:smallball`): the symmetric classifier
has expected error exactly `1/2`. -/
theorem null_risk {n m T : ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 2)
    (hB : γ * T ≤ 12) (ψ : Cube n → Vec m)
    (hψ : ∀ x, 7 / 16 ≤ ‖ψ x‖ ^ 2 ∧ ‖ψ x‖ ^ 2 ≤ 9 / 16) (D : Dist n) (h : Cube n → Bool) :
    ∫ b, err D (fun x => sgn (Zsym γ ψ D T x b)) h ∂(stdGaussian (Vec m)) = 1 / 2 := by
  set μ := stdGaussian (Vec m)
  have hmeas : ∀ (x : Cube n) (y : ℝ), MeasurableSet {b | sgn (Zsym γ ψ D T x b) ≠ y} :=
    fun x y => (measurable_sgn.comp (continuous_Zsym γ ψ D T x).measurable)
      (measurableSet_singleton y).compl
  have hpt : ∀ (x : Cube n) (y : Bool), μ.real {b | sgn (Zsym γ ψ D T x b) ≠ bsign y} = 1 / 2 := by
    intro x y
    set Z := Zsym γ ψ D T x with hZ
    have hZc : Continuous Z := continuous_Zsym γ ψ D T x
    set A := {b | Z b < 0} with hA_def
    have hA : MeasurableSet A := (isOpen_lt hZc continuous_const).measurableSet
    have hP : MeasurableSet {b | 0 < Z b} := (isOpen_lt continuous_const hZc).measurableSet
    have hsymm : μ A = μ {b | 0 < Z b} := by
      have hpre : A = (fun b => -b) ⁻¹' {b | 0 < Z b} := by
        ext b
        simp only [hA_def, Set.mem_ofPred_eq, Set.mem_preimage, hZ, Zsym_neg, neg_pos]
      rw [hpre, ← Measure.map_apply measurable_neg hP]
      congr 1
      have := stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := Vec m))
      rwa [LinearIsometryEquiv.coe_neg] at this
    have hzero : μ {b | Z b = 0} = 0 := by
      refine le_antisymm ?_ bot_le
      calc μ {b | Z b = 0} ≤ μ {b | |Z b| ≤ 0} :=
            measure_mono fun b hb => by simp only [Set.mem_ofPred_eq] at hb ⊢; rw [hb, abs_zero]
        _ ≤ ENNReal.ofReal (24 * 0) := smallball hγ0 hγ hB ψ hψ D x le_rfl
        _ = 0 := by simp
    have hcompl : μ Aᶜ = μ A := by
      apply le_antisymm
      · calc μ Aᶜ ≤ μ ({b | 0 < Z b} ∪ {b | Z b = 0}) := measure_mono fun b hb => by
              simp only [hA_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hb
              rcases hb.lt_or_eq with hb | hb
              · exact Or.inl hb
              · exact Or.inr hb.symm
          _ ≤ μ {b | 0 < Z b} + μ {b | Z b = 0} := measure_union_le _ _
          _ = μ A := by rw [hzero, add_zero, hsymm]
      · rw [hsymm]
        exact measure_mono fun b hb => by
          simp only [hA_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hb ⊢
          exact hb.le
    have hsum := measureReal_add_measureReal_compl (μ := μ) hA
    rw [probReal_univ] at hsum
    have hreal : μ.real Aᶜ = μ.real A := by simp only [measureReal_def, hcompl]
    have hA2 : μ.real A = 1 / 2 := by linarith
    cases y
    · have hset : {b | sgn (Z b) ≠ bsign false} = Aᶜ := by
        ext b
        simp only [hA_def, Set.mem_compl_iff, Set.mem_ofPred_eq, bsign, Bool.false_eq_true,
          ite_false]
        exact sgn_ne_neg_one (Z b)
      rw [hset, hreal, hA2]
    · have hset : {b | sgn (Z b) ≠ bsign true} = A := by
        ext b
        simp only [hA_def, Set.mem_ofPred_eq, bsign, ite_true]
        exact sgn_ne_one (Z b)
      rw [hset, hA2]
  have hint : ∀ b, err D (fun x => sgn (Zsym γ ψ D T x b)) h =
      ∑ x, D.p x * {b | sgn (Zsym γ ψ D T x b) ≠ bsign (h x)}.indicator 1 b := by
    intro b
    unfold err
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    by_cases hb : sgn (Zsym γ ψ D T x b) = bsign (h x) <;> simp [hb, Set.indicator]
  simp_rw [hint]
  have hintg : ∀ x ∈ Finset.univ, Integrable
      (fun b => D.p x * {b | sgn (Zsym γ ψ D T x b) ≠ bsign (h x)}.indicator 1 b) μ :=
    fun x _ => ((integrable_const (1 : ℝ)).indicator (hmeas x (bsign (h x)))).const_mul _
  rw [integral_finsetSum _ hintg]
  simp_rw [integral_const_mul, integral_indicator_one (hmeas _ _), hpt]
  rw [← Finset.sum_mul, D.sum_one, one_mul]

end GaussianSGD
