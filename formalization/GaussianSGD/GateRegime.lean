import GaussianSGD.GateMass

/-!
# The fixed-gate regime (`thm:gate`)

For a small total step, every gate at a cube point outside an initialization-defined set keeps
its initial sign along every labeled history. Outside that set the tail score is exactly linear
in the `mn` initial gated-coordinate features, and the set has small expected mass under every
fixed marginal. This yields a probabilistic-dimension bound.

Row movement is proved by induction on `t` with the addition formulas for `cosh` and `sinh`,
in place of the matrix-power expansion used in the paper.
-/

noncomputable section

open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

private lemma gr_norm_pt_sq {n : ℕ} (x : Cube n) : ‖pt x‖ ^ 2 = n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [pt, bsign]

private lemma gr_norm_pt {n : ℕ} (x : Cube n) : ‖pt x‖ = Real.sqrt n := by
  rw [← gr_norm_pt_sq x, Real.sqrt_sq (norm_nonneg _)]

private lemma gr_abs_g_le_one {y : ℝ} (hy : |y| ≤ 1) (z : ℝ) : |g y z| ≤ 1 := by
  unfold g
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + Real.exp (y * z))]
  rw [div_le_one (by positivity)]
  linarith [Real.exp_pos (y * z)]

private lemma gr_abs_relu_inner_le {n : ℕ} (w : Vec n) (x : Cube n) :
    |relu ⟪w, pt x⟫| ≤ ‖w‖ * Real.sqrt n := by
  rw [← gr_norm_pt x]
  refine le_trans ?_ (abs_real_inner_le_norm w (pt x))
  unfold relu
  rcases le_total ⟪w, pt x⟫ 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]


private lemma gr_traj_succ_snd {n m : ℕ} (η : ℝ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (t : ℕ) (j : Fin m) :
    (traj η θ0 xs ys (t + 1)).2 j = (traj η θ0 xs ys t).2 j +
      η * g (ys t) (score (traj η θ0 xs ys t) (xs t)) *
        relu ⟪(traj η θ0 xs ys t).1 j, pt (xs t)⟫ := by
  simp [traj, step, hid]

private lemma gr_traj_succ_fst {n m : ℕ} (η : ℝ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (t : ℕ) (j : Fin m) :
    (traj η θ0 xs ys (t + 1)).1 j = (traj η θ0 xs ys t).1 j +
      (η * g (ys t) (score (traj η θ0 xs ys t) (xs t)) * (traj η θ0 xs ys t).2 j *
        (if 0 < ⟪(traj η θ0 xs ys t).1 j, pt (xs t)⟫ then 1 else 0)) • pt (xs t) := by
  simp [traj, step]

/-- Row movement (`lem:rows`), for every labeled history with `|y_t| ≤ 1`. -/
theorem row_movement {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (θ0 : Params n m) (xs : ℕ → Cube n)
    (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (j : Fin m) (t : ℕ) :
    |(traj η θ0 xs ys t).2 j| ≤
        |θ0.2 j| * Real.cosh (t * η * Real.sqrt n) + ‖θ0.1 j‖ * Real.sinh (t * η * Real.sqrt n) ∧
    ‖(traj η θ0 xs ys t).1 j - θ0.1 j‖ ≤
        |θ0.2 j| * Real.sinh (t * η * Real.sqrt n) +
          ‖θ0.1 j‖ * (Real.cosh (t * η * Real.sqrt n) - 1) := by
  set l := η * Real.sqrt n with hl
  have hl0 : 0 ≤ l := mul_nonneg hη (Real.sqrt_nonneg _)
  have hmul : ∀ s : ℕ, (s : ℝ) * η * Real.sqrt n = s * l := fun s => by rw [hl, mul_assoc]
  simp only [hmul]
  have ha0 := abs_nonneg (θ0.2 j)
  have hw0 := norm_nonneg (θ0.1 j)
  induction t with
  | zero => simp [traj]
  | succ t ih =>
    obtain ⟨iha, ihw⟩ := ih
    set a := (traj η θ0 xs ys t).2 j
    set w := (traj η θ0 xs ys t).1 j
    set c := g (ys t) (score (traj η θ0 xs ys t) (xs t))
    have hc : |c| ≤ 1 := gr_abs_g_le_one (hys t) _
    have htl : 0 ≤ (t : ℝ) * l := mul_nonneg (Nat.cast_nonneg _) hl0
    have hs0 : 0 ≤ Real.sinh (t * l) := Real.sinh_nonneg_iff.mpr htl
    have hc0 : 0 ≤ Real.cosh (t * l) := (Real.cosh_pos _).le
    have hsl : l ≤ Real.sinh l := Real.self_le_sinh_iff.mpr hl0
    have hcl : 1 ≤ Real.cosh l := Real.one_le_cosh l
    have hadd : ((t + 1 : ℕ) : ℝ) * l = t * l + l := by push_cast; ring
    rw [hadd, Real.cosh_add, Real.sinh_add]
    have hw : ‖w‖ ≤ |θ0.2 j| * Real.sinh (t * l) + ‖θ0.1 j‖ * Real.cosh (t * l) := by
      have h2 : ‖w‖ ≤ ‖θ0.1 j‖ + ‖w - θ0.1 j‖ := by
        calc ‖w‖ = ‖θ0.1 j + (w - θ0.1 j)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have hsc := mul_le_mul_of_nonneg_left hcl hs0
    have hcc := mul_le_mul_of_nonneg_left hcl hc0
    have hss := mul_le_mul_of_nonneg_left hsl hs0
    have hcs := mul_le_mul_of_nonneg_left hsl hc0
    constructor
    · rw [gr_traj_succ_snd]
      have h1 : |η * c * relu ⟪w, pt (xs t)⟫| ≤ l * ‖w‖ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hη, hl]
        have := gr_abs_relu_inner_le w (xs t)
        calc η * |c| * |relu ⟪w, pt (xs t)⟫| ≤ η * 1 * (‖w‖ * Real.sqrt n) := by gcongr
          _ = η * Real.sqrt n * ‖w‖ := by ring
      have h2 := abs_add_le a (η * c * relu ⟪w, pt (xs t)⟫)
      have h3 : l * ‖w‖ ≤ l * (|θ0.2 j| * Real.sinh (t * l) + ‖θ0.1 j‖ * Real.cosh (t * l)) :=
        mul_le_mul_of_nonneg_left hw hl0
      nlinarith
    · rw [gr_traj_succ_fst]
      have h1 : ‖(η * c * a * (if 0 < ⟪w, pt (xs t)⟫ then 1 else 0)) • pt (xs t)‖ ≤ l * |a| := by
        rw [norm_smul, gr_norm_pt, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hη,
          hl]
        have hi : |(if 0 < ⟪w, pt (xs t)⟫ then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
        calc η * |c| * |a| * |(if 0 < ⟪w, pt (xs t)⟫ then (1:ℝ) else 0)| * Real.sqrt n
            ≤ η * 1 * |a| * 1 * Real.sqrt n := by gcongr
          _ = η * Real.sqrt n * |a| := by ring
      have h2 : ‖w + (η * c * a * (if 0 < ⟪w, pt (xs t)⟫ then 1 else 0)) • pt (xs t) - θ0.1 j‖
          ≤ ‖w - θ0.1 j‖ + ‖(η * c * a * (if 0 < ⟪w, pt (xs t)⟫ then 1 else 0)) • pt (xs t)‖ := by
        calc _ = ‖(w - θ0.1 j) +
              (η * c * a * (if 0 < ⟪w, pt (xs t)⟫ then 1 else 0)) • pt (xs t)‖ := by
              congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : l * |a| ≤ l * (|θ0.2 j| * Real.cosh (t * l) + ‖θ0.1 j‖ * Real.sinh (t * l)) :=
        mul_le_mul_of_nonneg_left iha hl0
      nlinarith


private lemma gr_inner_euc {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    ⟪u, v⟫ = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]; simp only [Real.inner_apply]

private lemma gr_score_eq {n m : ℕ} (θ : Params n m) (x : Cube n) :
    score θ x = ∑ j, θ.2 j * relu ⟪θ.1 j, pt x⟫ := by
  unfold score hid; rw [gr_inner_euc]

private lemma gr_inner_pt {n : ℕ} (w : Vec n) (x : Cube n) :
    ⟪w, pt x⟫ = ∑ i, w i * bsign (x i) := by
  simp [PiLp.inner_apply, pt, mul_comm]

/-- Fixed-gate regime (`thm:gate`), part 1: outside `𝔅`, every gate at `x` keeps its initial
nonzero sign up to time `T`, for every labeled history with `|y_t| ≤ 1`. -/
theorem gates_fixed {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) {T : ℕ} (θ0 : Params n m)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (x : Cube n)
    (hx : x ∉ gateSet (η * T * Real.sqrt n) θ0) {t : ℕ} (ht : t ≤ T) (j : Fin m) :
    ⟪θ0.1 j, pt x⟫ ≠ 0 ∧
      SignType.sign ⟪(traj η θ0 xs ys t).1 j, pt x⟫ = SignType.sign ⟪θ0.1 j, pt x⟫ := by
  simp only [gateSet, Set.mem_ofPred_eq, not_exists, not_le] at hx
  have hxj := hx j
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hτ : (t : ℝ) * η * Real.sqrt n ≤ η * T * Real.sqrt n := by
    have : (t : ℝ) ≤ T := by exact_mod_cast ht
    nlinarith [mul_nonneg hη hsq]
  have hτ0 : 0 ≤ (t : ℝ) * η * Real.sqrt n := by positivity
  have hsinh : Real.sinh (t * η * Real.sqrt n) ≤ Real.sinh (η * T * Real.sqrt n) :=
    Real.sinh_le_sinh.mpr hτ
  have hcosh : Real.cosh (t * η * Real.sqrt n) ≤ Real.cosh (η * T * Real.sqrt n) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hτ0, abs_of_nonneg (hτ0.trans hτ)]
    exact hτ
  have hmove := (row_movement hη θ0 xs ys hys j t).2
  have hdiff : |⟪(traj η θ0 xs ys t).1 j - θ0.1 j, pt x⟫| ≤
      Real.sqrt n * gateRadius (η * T * Real.sqrt n) θ0 j := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [gr_norm_pt, mul_comm]
    refine mul_le_mul_of_nonneg_left (hmove.trans ?_) hsq
    unfold gateRadius
    gcongr
  rw [inner_sub_left] at hdiff
  have hlt := lt_of_le_of_lt hdiff hxj
  rcases lt_trichotomy ⟪θ0.1 j, pt x⟫ 0 with h | h | h
  · rw [abs_of_neg h] at hlt
    have : ⟪(traj η θ0 xs ys t).1 j, pt x⟫ < 0 := by linarith [(abs_lt.mp hlt).2]
    exact ⟨h.ne, by rw [sign_neg this, sign_neg h]⟩
  · rw [h, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg _))
  · rw [abs_of_pos h] at hlt
    have : 0 < ⟪(traj η θ0 xs ys t).1 j, pt x⟫ := by linarith [(abs_lt.mp hlt).1]
    exact ⟨h.ne', by rw [sign_pos this, sign_pos h]⟩

private lemma gr_relu_eq_gate {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) {T : ℕ} (θ0 : Params n m)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (x : Cube n)
    (hx : x ∉ gateSet (η * T * Real.sqrt n) θ0) {t : ℕ} (ht : t ≤ T) (j : Fin m) :
    relu ⟪(traj η θ0 xs ys t).1 j, pt x⟫ =
      (if 0 < ⟪θ0.1 j, pt x⟫ then 1 else 0) * ⟪(traj η θ0 xs ys t).1 j, pt x⟫ := by
  simp only [gateSet, Set.mem_ofPred_eq, not_exists, not_le] at hx
  have hxj := hx j
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hτ : (t : ℝ) * η * Real.sqrt n ≤ η * T * Real.sqrt n := by
    have : (t : ℝ) ≤ T := by exact_mod_cast ht
    nlinarith [mul_nonneg hη hsq]
  have hτ0 : 0 ≤ (t : ℝ) * η * Real.sqrt n := by positivity
  have hsinh : Real.sinh (t * η * Real.sqrt n) ≤ Real.sinh (η * T * Real.sqrt n) :=
    Real.sinh_le_sinh.mpr hτ
  have hcosh : Real.cosh (t * η * Real.sqrt n) ≤ Real.cosh (η * T * Real.sqrt n) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hτ0, abs_of_nonneg (hτ0.trans hτ)]
    exact hτ
  have hmove := (row_movement hη θ0 xs ys hys j t).2
  have hdiff : |⟪(traj η θ0 xs ys t).1 j - θ0.1 j, pt x⟫| ≤
      Real.sqrt n * gateRadius (η * T * Real.sqrt n) θ0 j := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [gr_norm_pt, mul_comm]
    refine mul_le_mul_of_nonneg_left (hmove.trans ?_) hsq
    unfold gateRadius
    gcongr
  rw [inner_sub_left] at hdiff
  have hlt := lt_of_le_of_lt hdiff hxj
  unfold relu
  rcases lt_trichotomy ⟪θ0.1 j, pt x⟫ 0 with h | h | h
  · rw [ite_eq_right (not_lt.mpr h.le), zero_mul, max_eq_right]
    rw [abs_of_neg h] at hlt
    linarith [(abs_lt.mp hlt).2]
  · rw [h, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg _))
  · rw [ite_eq_left h, one_mul, max_eq_left]
    rw [abs_of_pos h] at hlt
    linarith [(abs_lt.mp hlt).1]

/-- Fixed-gate regime (`thm:gate`), exact representation: outside `𝔅`, for every labeled history, the
tail score equals `⟪C, φ_{W₀}(x)⟫`. -/
theorem exact_representation {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (T : ℕ) (θ0 : Params n m)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (x : Cube n)
    (hx : x ∉ gateSet (η * T * Real.sqrt n) θ0) :
    tailScore η T θ0 xs ys x = ⟪gateCoeff η T θ0 xs ys, gateFeat θ0.1 x⟫ := by
  have key : ∀ t ∈ tail T, score (traj η θ0 xs ys t) x =
      ∑ p : Fin m × Fin n, (traj η θ0 xs ys t).2 p.1 * (traj η θ0 xs ys t).1 p.1 p.2 *
        (bsign (x p.2) * if 0 < ⟪θ0.1 p.1, pt x⟫ then 1 else 0) := by
    intro t ht
    have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
    rw [Fintype.sum_prod_type, gr_score_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gr_relu_eq_gate hη θ0 xs ys hys x hx htT j, gr_inner_pt ((traj η θ0 xs ys t).1 j),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    ring
  unfold tailScore
  rw [Finset.sum_congr rfl key]
  unfold gateCoeff gateFeat
  rw [gr_inner_euc, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring



private lemma gr_cosh_lt_two {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) : Real.cosh τ < 2 := by
  have h1 : Real.cosh τ ≤ Real.exp (1 / 2) := (Real.cosh_le_exp_half_sq τ).trans
    (Real.exp_le_exp.mpr (by nlinarith))
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) < 4 := by
    rw [← Real.exp_add]; norm_num; linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2)]

private lemma gr_gateBound_nonneg (n m : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) :
    0 ≤ gateBound n m τ := by
  have hs : 0 ≤ Real.sinh τ := Real.sinh_nonneg_iff.mpr hτ0
  have hc : 0 ≤ Real.cosh τ - 1 := by linarith [Real.one_le_cosh τ]
  have h2 := gr_cosh_lt_two hτ0 hτ
  exact le_min zero_le_one (div_nonneg (by positivity) (by linarith))

private lemma gr_measurableSet_row {n m : ℕ} (τ : ℝ) (x : Cube n) (j : Fin m) :
    MeasurableSet {θ : Params n m | |⟪θ.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ j} := by
  unfold gateRadius
  exact measurableSet_le (by fun_prop) (by fun_prop)

private lemma gr_measurable_mass {n m : ℕ} (τ : ℝ) (D : Dist n) :
    Measurable fun θ : Params n m =>
      ENNReal.ofReal (∑ x, D.p x * (gateSet τ θ).indicator 1 x) := by
  have h : ∀ (θ : Params n m) x, (gateSet τ θ).indicator (1 : Cube n → ℝ) x =
      (⋃ j, {θ : Params n m | |⟪θ.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ j}).indicator 1 θ := by
    intro θ x
    have hmem : x ∈ gateSet τ θ ↔
        θ ∈ ⋃ j, {θ : Params n m | |⟪θ.1 j, pt x⟫| ≤ Real.sqrt n * gateRadius τ θ j} := by
      simp [gateSet]
    by_cases hx : x ∈ gateSet τ θ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hmem.mpr hx)]
  simp_rw [h]
  refine Measurable.ennreal_ofReal (Finset.measurable_sum _ fun x _ => ?_)
  exact measurable_const.mul (measurable_one.indicator
    (MeasurableSet.iUnion fun j => gr_measurableSet_row τ x j))

private lemma gr_err_nonneg {n : ℕ} (D : Dist n) (G : Cube n → ℝ) (h : Cube n → Bool) :
    0 ≤ err D G h :=
  Finset.sum_nonneg fun x _ => mul_nonneg (D.nonneg x) (by split_ifs <;> norm_num)

private lemma gr_sum_histWeight {n : ℕ} (D : Dist n) (T : ℕ) :
    ∑ s : Fin T → Cube n, histWeight D s = 1 := by
  unfold histWeight
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  simp [D.sum_one]

/-- Pathwise error transfer in the fixed-gate regime:
`err_D(sign⟪C, φ⟫, h) ≤ err_D(sign F, h) + D(𝔅)`. -/
private lemma gr_err_le {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (T : ℕ) (θ0 : Params n m)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) (D : Dist n) (h : Cube n → Bool) :
    err D (fun x => sgn ⟪gateCoeff η T θ0 xs ys, gateFeat θ0.1 x⟫) h ≤
      err D (fun x => sgn (tailScore η T θ0 xs ys x)) h +
        ∑ x, D.p x * (gateSet (η * T * Real.sqrt n) θ0).indicator 1 x := by
  unfold err
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (D.nonneg x)
  dsimp only
  by_cases hx : x ∈ gateSet (η * T * Real.sqrt n) θ0
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    have : (if sgn (tailScore η T θ0 xs ys x) = bsign (h x) then (0 : ℝ) else 1) ≥ 0 := by
      split_ifs <;> norm_num
    split_ifs <;> linarith
  · rw [Set.indicator_of_notMem hx, add_zero]
    simp only [exact_representation hη T θ0 xs ys hys x hx, le_refl]

/-- For every initialization, the best gated-coordinate classifier is at most the
conditional error of the process plus the mass of the exceptional set. -/
private lemma gr_inf_le {n m : ℕ} {η : ℝ} (hη : 0 ≤ η) (T : ℕ) (W : Fin m → Vec n) (a : Vec m)
    (D : Dist n) (h : Cube n → Bool) :
    (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h) ≤
      condErr η T (W, a) h D +
        ∑ x, D.p x * (gateSet (η * T * Real.sqrt n) (W, a)).indicator 1 x := by
  have hbdd : BddBelow (Set.range fun u : EuclideanSpace ℝ (Fin m × Fin n) =>
      err D (fun x => sgn ⟪u, gateFeat W x⟫) h) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact gr_err_nonneg _ _ _⟩
  have hw : ∀ s : Fin T → Cube n, 0 ≤ histWeight D s :=
    fun s => Finset.prod_nonneg fun i _ => D.nonneg _
  have hlab : ∀ s : Fin T → Cube n, ∀ t, |labels h (ext s) t| ≤ 1 := by
    intro s t; unfold labels bsign; split_ifs <;> norm_num
  set I := ⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h
  set M := ∑ x, D.p x * (gateSet (η * T * Real.sqrt n) (W, a)).indicator 1 x
  calc I = ∑ s : Fin T → Cube n, histWeight D s * I := by
        rw [← Finset.sum_mul, gr_sum_histWeight, one_mul]
    _ ≤ ∑ s : Fin T → Cube n, histWeight D s *
          (err D (fun x => sgn (tailScore η T (W, a) (ext s) (labels h (ext s)) x)) h + M) := by
        refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hw s)
        exact (ciInf_le hbdd (gateCoeff η T (W, a) (ext s) (labels h (ext s)))).trans
          (gr_err_le hη T (W, a) (ext s) (labels h (ext s)) (hlab s) D h)
    _ = condErr η T (W, a) h D + M := by
        rw [condErr]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, gr_sum_histWeight, one_mul]

/-- The point mass at `x₀`. -/
private def gr_point {n : ℕ} (x0 : Cube n) : Dist n where
  p := fun x => if x = x0 then 1 else 0
  nonneg := fun x => by split_ifs <;> norm_num
  sum_one := by simp

/-- If every gate is closed at `x₀`, training on `x₀` never moves the parameters. -/
private lemma gr_traj_closed {n m : ℕ} (η : ℝ) (θ0 : Params n m) (x0 : Cube n)
    (hclosed : ∀ j, ⟪θ0.1 j, pt x0⟫ ≤ 0) (xs : ℕ → Cube n) (ys : ℕ → ℝ) (T : ℕ)
    (hxs : ∀ t < T, xs t = x0) : ∀ t ≤ T, traj η θ0 xs ys t = θ0 := by
  have hhid : hid θ0.1 x0 = 0 := by
    ext j
    simp [hid, relu, max_eq_right (hclosed j)]
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have := ih (by omega)
    show step η (traj η θ0 xs ys t) (xs t) (ys t) = θ0
    rw [this, hxs t (by omega)]
    unfold step
    have h0 : ∀ j, ¬ (0 < ⟪θ0.1 j, pt x0⟫) := fun j => not_lt.mpr (hclosed j)
    simp [hhid, h0]

/-- The half-space `{w : ⟪w, v⟫ ≤ 0}` has positive `rowLaw` mass. -/
private lemma gr_rowLaw_halfspace_ne_zero (n : ℕ) (v : Vec n) :
    rowLaw n {w | ⟪w, v⟫ ≤ 0} ≠ 0 := by
  have hS : MeasurableSet {w : Vec n | ⟪w, v⟫ ≤ 0} := measurableSet_le (by fun_prop) (by fun_prop)
  have hneg : (rowLaw n).map (fun w => -w) = rowLaw n := by
    unfold rowLaw
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have : (fun w : Vec n => -w) ∘ (fun v : Vec n => (Real.sqrt n)⁻¹ • v) =
        (fun v => (Real.sqrt n)⁻¹ • v) ∘ (LinearIsometryEquiv.neg ℝ : Vec n ≃ₗᵢ[ℝ] Vec n) := by
      funext w; simp [LinearIsometryEquiv.coe_neg]
    rw [this, ← Measure.map_map (by fun_prop) (LinearIsometryEquiv.neg ℝ).continuous.measurable,
      stdGaussian_map]
  have hS' : MeasurableSet {w : Vec n | 0 ≤ ⟪w, v⟫} := measurableSet_le (by fun_prop) (by fun_prop)
  have hsym : rowLaw n {w | 0 ≤ ⟪w, v⟫} = rowLaw n {w | ⟪w, v⟫ ≤ 0} := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg hS']
    congr 1
    ext w; simp [inner_neg_left]
  intro h0
  have hu : (Set.univ : Set (Vec n)) ⊆ {w | ⟪w, v⟫ ≤ 0} ∪ {w | 0 ≤ ⟪w, v⟫} := by
    intro w _; rcases le_total ⟪w, v⟫ 0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have := (measure_mono hu).trans (measure_union_le _ _ (μ := rowLaw n))
  rw [hsym, h0, measure_univ] at this
  simp at this

/-- A target that is false at some point has positive risk under the point mass there. -/
private lemma gr_risk_pos {n m : ℕ} (η : ℝ) (T : ℕ) (h : Cube n → Bool) (x0 : Cube n)
    (hx0 : h x0 = false) : risk m η T h (gr_point x0) ≠ 0 := by
  set S : Set (Fin m → Vec n) := Set.univ.pi fun _ => {w | ⟪w, pt x0⟫ ≤ 0}
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => measurableSet_le (by fun_prop) (by fun_prop)
  have hSpos : hiddenLaw n m S ≠ 0 := by
    unfold hiddenLaw
    rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => gr_rowLaw_halfspace_ne_zero n (pt x0)
  have hcond : ∀ W ∈ S, ∀ a : Vec m, 1 ≤ condErr η T (W, a) h (gr_point x0) := by
    intro W hW a
    have hclosed : ∀ j, ⟪(W, a).1 j, pt x0⟫ ≤ 0 := fun j => hW j (Set.mem_univ j)
    set s0 : Fin T → Cube n := fun _ => x0
    have htraj := gr_traj_closed η (W, a) x0 hclosed (ext s0) (labels h (ext s0)) T
      (fun t ht => by simp [ext, ht, s0])
    have hF : tailScore η T (W, a) (ext s0) (labels h (ext s0)) x0 = 0 := by
      unfold tailScore
      rw [Finset.sum_congr rfl fun t ht => by rw [htraj t (Finset.mem_Icc.mp ht).2]]
      have : score (W, a) x0 = 0 := by
        rw [gr_score_eq]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [relu, max_eq_right (hclosed j)]
      simp [this]
    have hw0 : histWeight (gr_point x0) s0 = 1 := by simp [histWeight, gr_point, s0]
    have he0 : err (gr_point x0) (fun x => sgn (tailScore η T (W, a) (ext s0)
        (labels h (ext s0)) x)) h = 1 := by
      unfold err
      rw [Finset.sum_eq_single x0 (fun x _ hx => by simp [gr_point, hx]) (by simp)]
      simp [gr_point, hF, sgn, hx0, bsign]
      norm_num
    unfold condErr
    calc (1 : ℝ) = histWeight (gr_point x0) s0 * err (gr_point x0) (fun x => sgn (tailScore η T
          (W, a) (ext s0) (labels h (ext s0)) x)) h := by rw [hw0, he0, one_mul]
      _ ≤ _ := Finset.single_le_sum (f := fun s => histWeight (gr_point x0) s *
          err (gr_point x0) (fun x => sgn (tailScore η T (W, a) (ext s) (labels h (ext s)) x)) h)
          (fun s _ => mul_nonneg (Finset.prod_nonneg fun i _ => (gr_point x0).nonneg _)
            (gr_err_nonneg _ _ _)) (Finset.mem_univ s0)
  intro h0
  apply hSpos
  refine le_antisymm ?_ zero_le
  rw [← h0, ← lintegral_indicator_one hSm]
  unfold risk
  refine lintegral_mono fun W => ?_
  by_cases hW : W ∈ S
  · rw [Set.indicator_of_mem hW, Pi.one_apply]
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂(outLaw m) := by simp
      _ ≤ _ := lintegral_mono fun a => by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hcond W hW a)
  · rw [Set.indicator_of_notMem hW]; exact zero_le

/-- Fixed-gate regime (`thm:gate`), probabilistic dimension: if the process learns every target in `H` to
expected error `ε` under every marginal and `τ = η T √n ≤ 1`, the law of `φ_{W₀}`
witnesses `pdc_{ε + B_{n,m}(τ)}(H) ≤ mn`. -/
theorem gate_pdc {n m T : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 0 ≤ η)
    (hτ : η * T * Real.sqrt n ≤ 1) (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    ∀ h ∈ H, ∀ D : Dist n,
      ∫⁻ W, ENNReal.ofReal
          (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h)
        ∂(hiddenLaw n m) ≤ ENNReal.ofReal (ε + gateBound n m (η * T * Real.sqrt n)) := by
  intro h hh D
  set τ := η * T * Real.sqrt n with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hgB := gr_gateBound_nonneg n m hτ0 hτ
  rcases le_or_gt 0 ε with hε | hε
  · set G : Params n m → ℝ≥0∞ := fun θ =>
      ENNReal.ofReal (∑ x, D.p x * (gateSet τ θ).indicator 1 x) with hG
    have hGm : Measurable G := gr_measurable_mass τ D
    have hW : ∀ W : Fin m → Vec n, ENNReal.ofReal
        (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h) ≤
        ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) +
          ∫⁻ a, G (W, a) ∂(outLaw m) := by
      intro W
      have hGW : Measurable fun a => G (W, a) := hGm.comp measurable_prodMk_left
      rw [← lintegral_add_right' _ hGW.aemeasurable]
      calc _ = ∫⁻ _, ENNReal.ofReal (⨅ u : EuclideanSpace ℝ (Fin m × Fin n),
            err D (fun x => sgn ⟪u, gateFeat W x⟫) h) ∂(outLaw m) := by simp
        _ ≤ _ := lintegral_mono fun a =>
            (ENNReal.ofReal_le_ofReal (gr_inf_le hη T W a D h)).trans (ENNReal.ofReal_add_le)
    calc _ ≤ ∫⁻ W, (∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) +
          ∫⁻ a, G (W, a) ∂(outLaw m)) ∂(hiddenLaw n m) := lintegral_mono hW
      _ = risk m η T h D + ∫⁻ W, ∫⁻ a, G (W, a) ∂(outLaw m) ∂(hiddenLaw n m) := by
          rw [lintegral_add_right' _ hGm.lintegral_prod_right'.aemeasurable]; rfl
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (gateBound n m τ) :=
          add_le_add (hprem h hh D) (gateSet_mass hn hτ0 hτ D)
      _ = _ := (ENNReal.ofReal_add hε hgB).symm
  · -- For `ε < 0` the premise forces zero risk, which fails at a point mass where `h` is false.
    by_cases hall : ∀ x, h x = true
    · have h0 : ∀ W : Fin m → Vec n, ENNReal.ofReal
          (⨅ u : EuclideanSpace ℝ (Fin m × Fin n),
            err D (fun x => sgn ⟪u, gateFeat W x⟫) h) = 0 := by
        intro W
        rw [ENNReal.ofReal_eq_zero]
        have hbdd : BddBelow (Set.range fun u : EuclideanSpace ℝ (Fin m × Fin n) =>
            err D (fun x => sgn ⟪u, gateFeat W x⟫) h) :=
          ⟨0, by rintro _ ⟨u, rfl⟩; exact gr_err_nonneg _ _ _⟩
        refine (ciInf_le hbdd 0).trans (le_of_eq ?_)
        simp [err, sgn, hall, bsign]
      simp [h0]
    · simp only [not_forall] at hall
      obtain ⟨x0, hx0⟩ := hall
      have hx0' : h x0 = false := by simpa using hx0
      have := hprem h hh (gr_point x0)
      rw [ENNReal.ofReal_of_nonpos hε.le, nonpos_iff_eq_zero] at this
      exact absurd this (gr_risk_pos η T h x0 hx0')

/-- Fixed-gate regime (`thm:gate`), small-step form: `η ≤ 1/m` and `m ≥ 16 n² T² / δ²` give
`pdc_{ε + δ}(H) ≤ mn`. -/
theorem gate_small_step {n m T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / m) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1) (hm : 16 * n ^ 2 * T ^ 2 / δ ^ 2 ≤ m)
    (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    ∀ h ∈ H, ∀ D : Dist n,
      ∫⁻ W, ENNReal.ofReal
          (⨅ u : EuclideanSpace ℝ (Fin m × Fin n), err D (fun x => sgn ⟪u, gateFeat W x⟫) h)
        ∂(hiddenLaw n m) ≤ ENNReal.ofReal (ε + δ) := by
  intro h hh D
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set r := Real.sqrt n with hr
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; exact hnR
  have hrr : r ^ 2 = n := Real.sq_sqrt (by positivity)
  have hm16 : 16 * (n : ℝ) ^ 2 * T ^ 2 ≤ δ ^ 2 * m := by
    rw [div_le_iff₀ (by positivity)] at hm; linarith
  have hm0 : (0 : ℝ) < m := by
    have : (0 : ℝ) < 16 * n ^ 2 * T ^ 2 := by positivity
    nlinarith [sq_nonneg δ]
  set s := Real.sqrt m with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hm0
  have hss : s ^ 2 = m := Real.sq_sqrt hm0.le
  have hk : 4 * r ^ 2 * T ≤ δ * s := by
    have h1 : (4 * r ^ 2 * T) ^ 2 ≤ (δ * s) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hrr, hss]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  set τ := η * T * r with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  have hηm : η * m ≤ 1 := by rw [le_div_iff₀ hm0] at hη; linarith
  have hτs : τ * s ^ 2 ≤ T * r := by
    rw [hss, hτdef]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Real.sqrt_nonneg n)]
  have hA : r * s * τ ≤ δ / 4 := by
    have h1 : r * s * τ * s ≤ δ / 4 * s := by nlinarith
    exact le_of_mul_le_mul_right h1 hs0
  have hrs : 1 ≤ r * s := by
    have : 4 ≤ δ * s := by nlinarith
    nlinarith
  have hτ1 : τ ≤ 1 := by nlinarith
  refine (gate_pdc hn hη0 hτ1 H hprem h hh D).trans (ENNReal.ofReal_le_ofReal ?_)
  have hgb := gateBound_le (m := m) hn hτ0 hτ1
  rw [Real.sqrt_mul (Nat.cast_nonneg n), ← hr, ← hs] at hgb
  have hB2 : (m : ℝ) * r * τ ^ 2 ≤ (r * s * τ) ^ 2 := by
    rw [← hss]
    have : 0 ≤ s ^ 2 * τ ^ 2 := by positivity
    nlinarith
  nlinarith [sq_nonneg (r * s * τ), mul_nonneg (mul_nonneg (zero_le_one.trans hr1) hs0.le) hτ0]

end GaussianSGD
