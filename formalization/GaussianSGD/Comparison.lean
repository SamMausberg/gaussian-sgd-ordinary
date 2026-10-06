import GaussianSGD.Defs

/-!
# Score comparison through gate changes (`lem:score`)

On the good event for the hidden layer and with `‖a₀‖ ≤ 2`, the exact network's
score stays within `κ = 544 n / m` of the frozen-feature linear recurrence, for every
labeled history and every cube point. No gate-stability assumption is used.

The movement of both layers is bounded by induction on `t`, in place of the bootstrap
over the maxima `A` and `D_W` used in the paper.
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace GaussianSGD

private lemma cmp_norm_pt_sq {n : ℕ} (x : Cube n) : ‖pt x‖ ^ 2 = n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [pt, bsign]

private lemma cmp_norm_pt {n : ℕ} (x : Cube n) : ‖pt x‖ = Real.sqrt n := by
  rw [← cmp_norm_pt_sq x, Real.sqrt_sq (norm_nonneg _)]

private lemma cmp_abs_g_le_one {y : ℝ} (hy : |y| ≤ 1) (z : ℝ) : |g y z| ≤ 1 := by
  unfold g
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 1 + Real.exp (y * z)),
    div_le_one (by positivity)]
  linarith [Real.exp_pos (y * z)]

private lemma cmp_g_one (z : ℝ) : g 1 z = (1 + Real.exp z)⁻¹ := by simp [g]

private lemma cmp_g_neg_one (z : ℝ) : g (-1) z = (1 + Real.exp z)⁻¹ - 1 := by
  unfold g
  rw [neg_one_mul, Real.exp_neg]
  have h := Real.exp_pos z
  field_simp
  ring

private lemma cmp_logistic_anti {p q : ℝ} (h : q ≤ p) :
    (1 + Real.exp p)⁻¹ ≤ (1 + Real.exp q)⁻¹ := by
  gcongr

private lemma cmp_logistic_lip (p q : ℝ) :
    |(1 + Real.exp p)⁻¹ - (1 + Real.exp q)⁻¹| ≤ |p - q| / 4 := by
  wlog hpq : q < p generalizing p q
  · rcases (not_lt.mp hpq).eq_or_lt with h | h
    · subst h; simp
    · rw [abs_sub_comm, abs_sub_comm p q]; exact this q p h
  have hd : ∀ z, HasDerivAt (fun z => (1 + Real.exp z)⁻¹)
      (-Real.exp z / (1 + Real.exp z) ^ 2) z := by
    intro z
    exact ((Real.hasDerivAt_exp z).const_add 1).inv (by positivity)
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun z => (1 + Real.exp z)⁻¹)
    (fun z => -Real.exp z / (1 + Real.exp z) ^ 2) hpq
    (fun z _ => (hd z).continuousAt.continuousWithinAt) (fun z _ => hd z)
  have hpq' : 0 < p - q := sub_pos.mpr hpq
  have heq : (1 + Real.exp p)⁻¹ - (1 + Real.exp q)⁻¹ =
      (-Real.exp c / (1 + Real.exp c) ^ 2) * (p - q) := by
    rw [hc]; field_simp
  rw [heq, abs_mul, abs_of_pos hpq']
  have hec := Real.exp_pos c
  have hb : |-Real.exp c / (1 + Real.exp c) ^ 2| ≤ 1 / 4 := by
    rw [abs_div, abs_neg, abs_of_pos hec, abs_of_pos (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.exp c - 1)]
  nlinarith

private lemma cmp_g_lip {y : ℝ} (hy : y = 1 ∨ y = -1) (p q : ℝ) :
    |g y p - g y q| ≤ |p - q| / 4 := by
  rcases hy with rfl | rfl
  · rw [cmp_g_one, cmp_g_one]; exact cmp_logistic_lip p q
  · rw [cmp_g_neg_one, cmp_g_neg_one, sub_sub_sub_cancel_right]; exact cmp_logistic_lip p q

private lemma cmp_g_anti {y : ℝ} (hy : y = 1 ∨ y = -1) (p q : ℝ) :
    (g y p - g y q) * (p - q) ≤ 0 := by
  have key : ((1 + Real.exp p)⁻¹ - (1 + Real.exp q)⁻¹) * (p - q) ≤ 0 := by
    rcases le_total q p with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (cmp_logistic_anti h))
        (sub_nonneg.mpr h)
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (cmp_logistic_anti h))
        (sub_nonpos.mpr h)
  rcases hy with rfl | rfl
  · rw [cmp_g_one, cmp_g_one]; exact key
  · rw [cmp_g_neg_one, cmp_g_neg_one, sub_sub_sub_cancel_right]; exact key

/-- The frozen sample map `v ↦ v + γ g(y, ⟪v, ψ⟫) ψ` is nonexpansive when `γ‖ψ‖² ≤ 2`. -/
private lemma cmp_sample_nonexp {m : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (ψ : Vec m) (hψ : γ * ‖ψ‖ ^ 2 ≤ 2)
    {y : ℝ} (hy : y = 1 ∨ y = -1) (v w : Vec m) :
    ‖(v + (γ * g y ⟪v, ψ⟫) • ψ) - (w + (γ * g y ⟪w, ψ⟫) • ψ)‖ ≤ ‖v - w‖ := by
  set Δ := g y ⟪v, ψ⟫ - g y ⟪w, ψ⟫
  set δ := ⟪v - w, ψ⟫
  have hδ : δ = ⟪v, ψ⟫ - ⟪w, ψ⟫ := inner_sub_left _ _ _
  have hexp : (v + (γ * g y ⟪v, ψ⟫) • ψ) - (w + (γ * g y ⟪w, ψ⟫) • ψ) =
      (v - w) + (γ * Δ) • ψ := by
    simp only [Δ, mul_sub, sub_smul]; abel
  rw [hexp]
  have hlip : |Δ| ≤ |δ| / 4 := by rw [hδ]; exact cmp_g_lip hy _ _
  have hanti : Δ * δ ≤ 0 := by rw [hδ]; exact cmp_g_anti hy _ _
  have hsq : ‖(v - w) + (γ * Δ) • ψ‖ ^ 2 ≤ ‖v - w‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h1 : Δ ^ 2 ≤ -(Δ * δ) / 4 := by
      have : |Δ| * |Δ| ≤ |Δ| * (|δ| / 4) := mul_le_mul_of_nonneg_left hlip (abs_nonneg _)
      have h2 : |Δ| * |δ| = -(Δ * δ) := by rw [← abs_mul, abs_of_nonpos hanti]
      nlinarith [sq_abs Δ]
    have h3 : (γ * Δ) ^ 2 * ‖ψ‖ ^ 2 = γ * Δ ^ 2 * (γ * ‖ψ‖ ^ 2) := by ring
    rw [h3]
    have h4 : γ * Δ ^ 2 * (γ * ‖ψ‖ ^ 2) ≤ γ * Δ ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hψ (by positivity)
    have h5 : γ * Δ ^ 2 ≤ γ * (-(Δ * δ) / 4) := mul_le_mul_of_nonneg_left h1 hγ0
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq


/-- The Frobenius norm of a matrix given by its rows. -/
private def cmpFro {n m : ℕ} (V : Fin m → Vec n) : ℝ :=
  ‖(WithLp.toLp 2 V : PiLp 2 (fun _ : Fin m => Vec n))‖

private lemma cmpFro_sq {n m : ℕ} (V : Fin m → Vec n) : cmpFro V ^ 2 = ∑ j, ‖V j‖ ^ 2 := by
  unfold cmpFro; rw [PiLp.norm_sq_eq_of_L2]

private lemma cmpFro_nonneg {n m : ℕ} (V : Fin m → Vec n) : 0 ≤ cmpFro V := norm_nonneg _

private lemma cmpFro_add_le {n m : ℕ} (V U : Fin m → Vec n) :
    cmpFro (V + U) ≤ cmpFro V + cmpFro U := by
  unfold cmpFro; rw [WithLp.toLp_add]; exact norm_add_le _ _

private lemma cmp_relu_lip (a b : ℝ) : |relu a - relu b| ≤ |a - b| := abs_max_sub_max_le_abs a b 0

private lemma cmp_hid_sub_le {n m : ℕ} (W W0 : Fin m → Vec n) (x : Cube n) :
    ‖hid W x - hid W0 x‖ ≤ Real.sqrt n * cmpFro (fun j => W j - W0 j) := by
  have hsq : ‖hid W x - hid W0 x‖ ^ 2 ≤ (Real.sqrt n * cmpFro (fun j => W j - W0 j)) ^ 2 := by
    rw [mul_pow, cmpFro_sq, Real.sq_sqrt (Nat.cast_nonneg n), EuclideanSpace.norm_sq_eq,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [hid, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    have h1 := cmp_relu_lip ⟪W j, pt x⟫ ⟪W0 j, pt x⟫
    have h2 : |⟪W j, pt x⟫ - ⟪W0 j, pt x⟫| ≤ ‖W j - W0 j‖ * Real.sqrt n := by
      rw [← inner_sub_left, ← cmp_norm_pt x]; exact abs_real_inner_le_norm _ _
    have h3 : (relu ⟪W j, pt x⟫ - relu ⟪W0 j, pt x⟫) ^ 2 ≤ (‖W j - W0 j‖ * Real.sqrt n) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (relu ⟪W j, pt x⟫ - relu ⟪W0 j, pt x⟫)])
        (by linarith [le_abs_self (relu ⟪W j, pt x⟫ - relu ⟪W0 j, pt x⟫)])
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at h3
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity [cmpFro_nonneg (fun j => W j - W0 j)])
    two_ne_zero).mp hsq

private lemma cmp_hid_eq_psi {n m : ℕ} (W : Fin m → Vec n) (x : Cube n) (hm : 0 < m) :
    hid W x = Real.sqrt m • psi W x := by
  unfold psi
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne', one_smul]

private lemma cmp_norm_hid_le {n m : ℕ} (W : Fin m → Vec n) (hψ : ∀ x, ‖psi W x‖ ^ 2 ≤ 9 / 16)
    (x : Cube n) (hm : 0 < m) : ‖hid W x‖ ≤ 3 / 4 * Real.sqrt m := by
  rw [cmp_hid_eq_psi W x hm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  nlinarith [hψ x, norm_nonneg (psi W x)]

private lemma cmp_traj_succ {n m : ℕ} (η : ℝ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (t : ℕ) :
    traj η θ0 xs ys (t + 1) = step η (traj η θ0 xs ys t) (xs t) (ys t) := rfl

/-- Arithmetic used for the movement bound. -/
private lemma cmp_move_arith {n m : ℝ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (hβm : β * m ≤ 12) : β * (3 / 4 * Real.sqrt m) + 4 * β ^ 2 * n ≤ 2 := by
  have hm0 : 0 < m := by linarith
  have hs := Real.sq_sqrt hm0.le
  have hs24 : 24 ≤ Real.sqrt m := by
    rw [Real.le_sqrt (by norm_num) hm0.le]; nlinarith
  have h1 : β * Real.sqrt m ≤ 1 / 2 := by
    have : β * Real.sqrt m * Real.sqrt m ≤ 12 := by nlinarith
    nlinarith
  have h2 : β ^ 2 * n ≤ 1 / 4 := by
    have h3 : β ^ 2 * m ^ 2 ≤ 144 := by nlinarith [mul_nonneg hβ hm0.le]
    have h4 : β ^ 2 * n * m ^ 2 ≤ 144 * n := by nlinarith
    have h5 : 144 * n ≤ m ^ 2 / 4 := by nlinarith
    nlinarith [sq_nonneg β]
  nlinarith

/-- Movement of both layers along the exact trajectory (`lem:score`, first step). -/
private lemma cmp_movement {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 ≤ η)
    (hB : η * m * T ≤ 12) (θ0 : Params n m) (hψ : ∀ x, ‖psi θ0.1 x‖ ^ 2 ≤ 9 / 16)
    (ha : ‖θ0.2‖ ≤ 2) (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1) :
    ∀ t ≤ T, ‖(traj η θ0 xs ys t).2 - θ0.2‖ ≤
        η * t * (3 / 4 * Real.sqrt m) + 4 * η ^ 2 * n * t ^ 2 ∧
      cmpFro (fun j => (traj η θ0 xs ys t).1 j - θ0.1 j) ≤ 4 * η * t * Real.sqrt n := by
  have hm0 : 0 < m := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : 576 * (n : ℝ) ≤ m := by exact_mod_cast hm
  have hsn := Real.sqrt_nonneg (n : ℝ)
  have hsnn := Real.sq_sqrt (Nat.cast_nonneg n)
  intro t ht
  induction t with
  | zero => simp [traj, cmpFro]; rfl
  | succ t ih =>
    obtain ⟨iha, ihw⟩ := ih (by omega)
    have htT : (t : ℝ) ≤ T := by exact_mod_cast (by omega : t ≤ T)
    have hat : ‖(traj η θ0 xs ys t).2‖ ≤ 4 := by
      have h1 : η * t * m ≤ 12 := by
        have : η * t * m ≤ η * m * T := by nlinarith [mul_nonneg hη (Nat.cast_nonneg m)]
        linarith
      have h2 := cmp_move_arith hnR hmR (mul_nonneg hη (Nat.cast_nonneg t)) h1
      have h3 : ‖(traj η θ0 xs ys t).2‖ ≤ ‖θ0.2‖ + ‖(traj η θ0 xs ys t).2 - θ0.2‖ := by
        calc _ = ‖θ0.2 + ((traj η θ0 xs ys t).2 - θ0.2)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      nlinarith
    set θ := traj η θ0 xs ys t with hθ
    set c := g (ys t) (score θ (xs t))
    have hc : |c| ≤ 1 := cmp_abs_g_le_one (hys t) _
    rw [cmp_traj_succ, ← hθ]
    constructor
    · have hhid : ‖hid θ.1 (xs t)‖ ≤
          3 / 4 * Real.sqrt m + Real.sqrt n * (4 * η * t * Real.sqrt n) := by
        have h1 := cmp_hid_sub_le θ.1 θ0.1 (xs t)
        have h2 := cmp_norm_hid_le θ0.1 hψ (xs t) hm0
        have h3 : ‖hid θ.1 (xs t)‖ ≤ ‖hid θ0.1 (xs t)‖ + ‖hid θ.1 (xs t) - hid θ0.1 (xs t)‖ := by
          calc _ = ‖hid θ0.1 (xs t) + (hid θ.1 (xs t) - hid θ0.1 (xs t))‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        have h4 := mul_le_mul_of_nonneg_left ihw hsn
        linarith
      have hstep : (step η θ (xs t) (ys t)).2 - θ0.2 = (θ.2 - θ0.2) + (η * c) • hid θ.1 (xs t) := by
        simp only [step, c]; abel
      rw [hstep]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hη]
      have h5 : η * |c| * ‖hid θ.1 (xs t)‖ ≤
          η * (3 / 4 * Real.sqrt m + Real.sqrt n * (4 * η * t * Real.sqrt n)) := by
        calc η * |c| * ‖hid θ.1 (xs t)‖ ≤ η * 1 * ‖hid θ.1 (xs t)‖ := by gcongr
          _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hhid hη
      push_cast
      have h6 : Real.sqrt n * (4 * η * t * Real.sqrt n) = 4 * η * t * n := by
        rw [mul_comm, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
      rw [h6] at h5
      nlinarith [mul_nonneg (mul_nonneg hη hη) (Nat.cast_nonneg n),
        mul_nonneg hη (Nat.cast_nonneg t)]
    · have hstep : (fun j => (step η θ (xs t) (ys t)).1 j - θ0.1 j) = (fun j => θ.1 j - θ0.1 j) +
          (fun j => (η * c * θ.2 j * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then 1 else 0)) • pt (xs t)) := by
        funext j; simp only [step, c, Pi.add_apply]; abel
      rw [hstep]
      refine (cmpFro_add_le _ _).trans ?_
      have hinc : cmpFro (fun j => (η * c * θ.2 j * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then 1 else 0)) •
          pt (xs t)) ≤ 4 * η * Real.sqrt n := by
        have hsq : cmpFro (fun j => (η * c * θ.2 j * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then 1 else 0)) •
            pt (xs t)) ^ 2 ≤ (4 * η * Real.sqrt n) ^ 2 := by
          rw [cmpFro_sq]
          have hj : ∀ j,
              ‖(η * c * θ.2 j * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then 1 else 0)) • pt (xs t)‖ ^ 2
                ≤ η ^ 2 * n * θ.2 j ^ 2 := by
            intro j
            rw [norm_smul, mul_pow, cmp_norm_pt_sq, Real.norm_eq_abs, sq_abs]
            have hi : (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0) ^ 2 ≤ 1 := by
              split_ifs <;> norm_num
            have hc2 : c ^ 2 ≤ 1 := by
              rw [← sq_abs]; nlinarith [abs_nonneg c]
            have : (η * c * θ.2 j * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0)) ^ 2 =
                η ^ 2 * θ.2 j ^ 2 *
                  (c ^ 2 * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0) ^ 2) := by
              ring
            rw [this]
            have h0 : 0 ≤ η ^ 2 * θ.2 j ^ 2 := by positivity
            have : c ^ 2 * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0) ^ 2 ≤ 1 := by
              nlinarith [sq_nonneg c, sq_nonneg (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0)]
            calc η ^ 2 * θ.2 j ^ 2 * (c ^ 2 * (if 0 < ⟪θ.1 j, pt (xs t)⟫ then (1 : ℝ) else 0) ^ 2)
                  * n ≤ η ^ 2 * θ.2 j ^ 2 * 1 * n := by gcongr
              _ = η ^ 2 * n * θ.2 j ^ 2 := by ring
          refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
          rw [← Finset.mul_sum]
          have hnorm : ∑ j, θ.2 j ^ 2 = ‖θ.2‖ ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
          rw [hnorm, mul_pow, mul_pow, hsnn]
          have : ‖θ.2‖ ^ 2 ≤ 16 := by nlinarith [norm_nonneg θ.2]
          nlinarith [mul_nonneg (sq_nonneg η) (Nat.cast_nonneg (α := ℝ) n)]
        exact (pow_le_pow_iff_left₀ (cmpFro_nonneg _) (by positivity) two_ne_zero).mp hsq
      push_cast
      linarith


/-- Uniform bounds on `‖a_t‖`, `e_t(x)` and `r_t(x)` along the exact trajectory. -/
private lemma cmp_residuals {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 ≤ η)
    (hB : η * m * T ≤ 12) (θ0 : Params n m) (hψ : ∀ x, ‖psi θ0.1 x‖ ^ 2 ≤ 9 / 16)
    (ha : ‖θ0.2‖ ≤ 2) (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, |ys t| ≤ 1)
    (t : ℕ) (ht : t ≤ T) (x : Cube n) :
    ‖(traj η θ0 xs ys t).2‖ ≤ 4 ∧
      ‖psi (traj η θ0 xs ys t).1 x - psi θ0.1 x‖ ≤ 4 * (η * T) * n / Real.sqrt m ∧
      |score (traj η θ0 xs ys t) x - ⟪Real.sqrt m • (traj η θ0 xs ys t).2, psi θ0.1 x⟫|
        ≤ 16 * (η * T) * n := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR' : 576 * (n : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hA, hW⟩ := cmp_movement hn hm hη hB θ0 hψ ha xs ys hys t ht
  have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hβ : η * t ≤ η * T := mul_le_mul_of_nonneg_left htT hη
  set θ := traj η θ0 xs ys t
  have hat : ‖θ.2‖ ≤ 4 := by
    have h1 : η * t * m ≤ 12 := by nlinarith
    have h2 := cmp_move_arith hnR hmR' (mul_nonneg hη (Nat.cast_nonneg t)) h1
    have h3 : ‖θ.2‖ ≤ ‖θ0.2‖ + ‖θ.2 - θ0.2‖ := by
      calc _ = ‖θ0.2 + (θ.2 - θ0.2)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith
  have hpsi : ‖psi θ.1 x - psi θ0.1 x‖ ≤ 4 * (η * T) * n / Real.sqrt m := by
    unfold psi
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsm),
      inv_mul_eq_div, div_le_div_iff_of_pos_right hsm]
    refine (cmp_hid_sub_le θ.1 θ0.1 x).trans ?_
    have h1 := mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg n)
    have h2 : Real.sqrt n * (4 * η * t * Real.sqrt n) = 4 * (η * t) * n := by
      rw [mul_comm, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]; ring
    have h3 : 4 * (η * t) * n ≤ 4 * (η * T) * n := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    linarith
  refine ⟨hat, hpsi, ?_⟩
  have hscore : score θ x = ⟪Real.sqrt m • θ.2, psi θ.1 x⟫ := by
    unfold score psi
    rw [inner_smul_left, inner_smul_right, conj_trivial, ← mul_assoc,
      mul_inv_cancel₀ hsm.ne', one_mul]
  rw [hscore, ← inner_sub_right]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsm]
  calc Real.sqrt m * ‖θ.2‖ * ‖psi θ.1 x - psi θ0.1 x‖
      ≤ Real.sqrt m * 4 * (4 * (η * T) * n / Real.sqrt m) := by gcongr
    _ = 16 * (η * T) * n := by field_simp; ring

/-- Arithmetic for the final constant of `lem:score`. -/
private lemma cmp_final_arith {n m : ℝ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {β : ℝ} (hβ : 0 ≤ β)
    (hβm : β * m ≤ 12) :
    16 * β * n + 3 / 4 * (β * m) * (3 / 16 * (16 * β * n) + 4 * β * n / Real.sqrt m)
      ≤ 544 * n / m := by
  have hm0 : 0 < m := by linarith
  have hs := Real.sq_sqrt hm0.le
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hs24 : 24 ≤ Real.sqrt m := by
    rw [Real.le_sqrt (by norm_num) hm0.le]; nlinarith
  set L := β * m with hL
  have hL0 : 0 ≤ L := mul_nonneg hβ hm0.le
  have hβ' : β = L / m := by rw [hL]; field_simp
  rw [hβ']
  have e1 : 4 * (L / m) * n / Real.sqrt m ≤ (L / m) * n / 6 := by
    rw [div_le_iff₀ hsm]
    have : 0 ≤ L / m * n := by positivity
    nlinarith
  have e2 : 16 * (L / m) * n +
        3 / 4 * L * (3 / 16 * (16 * (L / m) * n) + 4 * (L / m) * n / Real.sqrt m)
      ≤ 16 * (L / m) * n + 3 / 4 * L * (3 / 16 * (16 * (L / m) * n) + (L / m) * n / 6) := by
    gcongr
  refine e2.trans ?_
  rw [show 16 * (L / m) * n + 3 / 4 * L * (3 / 16 * (16 * (L / m) * n) + (L / m) * n / 6) =
    (16 * L + 19 / 8 * L ^ 2) * n / m by field_simp; ring]
  gcongr
  nlinarith


/-- Distance between the rescaled output layer `b_t = √m a_t` and the frozen recurrence. -/
private lemma cmp_frozen_gap {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 ≤ η)
    (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (θ0 : Params n m)
    (hψ : ∀ x, ‖psi θ0.1 x‖ ^ 2 ≤ 9 / 16) (ha : ‖θ0.2‖ ≤ 2) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (hys : ∀ t, ys t = 1 ∨ ys t = -1) :
    ∀ t ≤ T, ‖Real.sqrt m • (traj η θ0 xs ys t).2 - frozen (η * m) (psi θ0.1) xs ys
        (Real.sqrt m • θ0.2) t‖ ≤
      t * (η * m) * (3 / 16 * (16 * (η * T) * n) + 4 * (η * T) * n / Real.sqrt m) := by
  have hys' : ∀ t, |ys t| ≤ 1 := fun t => by rcases hys t with h | h <;> simp [h]
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hγ0 : 0 ≤ η * m := mul_nonneg hη hmR.le
  set γ := η * (m : ℝ) with hγdef
  set K := 3 / 16 * (16 * (η * T) * n) + 4 * (η * T) * n / Real.sqrt m with hK
  intro t ht
  induction t with
  | zero => simp [traj, frozen]
  | succ t ih =>
    have htT : t ≤ T := by omega
    have ih := ih htT
    obtain ⟨-, hpsi, hres⟩ := cmp_residuals hn hm hη hB θ0 hψ ha xs ys hys' t htT (xs t)
    set θ := traj η θ0 xs ys t with hθ
    set u := frozen γ (psi θ0.1) xs ys (Real.sqrt m • θ0.2) t
    set p := psi θ0.1 (xs t)
    set q := psi θ.1 (xs t)
    set b := Real.sqrt m • θ.2
    set c := g (ys t) (score θ (xs t))
    set c' := g (ys t) ⟪b, p⟫
    have hp : ‖p‖ ≤ 3 / 4 := by nlinarith [hψ (xs t), norm_nonneg p]
    have hb_succ : Real.sqrt m • (traj η θ0 xs ys (t + 1)).2 = b + (γ * c) • q := by
      rw [cmp_traj_succ, ← hθ]
      simp only [step, b, q, psi, smul_add, smul_smul]
      congr 2
      rw [hγdef]
      field_simp
      rw [Real.sq_sqrt hmR.le]
      show _ = η * m * g (ys t) (score θ (xs t))
      ring
    have hu_succ : frozen γ (psi θ0.1) xs ys (Real.sqrt m • θ0.2) (t + 1) =
        u + (γ * g (ys t) ⟪u, p⟫) • p := rfl
    rw [hb_succ, hu_succ]
    have hsplit : b + (γ * c) • q - (u + (γ * g (ys t) ⟪u, p⟫) • p) =
        ((b + (γ * c') • p) - (u + (γ * g (ys t) ⟪u, p⟫) • p)) +
          γ • ((c - c') • p + c • (q - p)) := by
      simp only [smul_add, smul_sub, smul_smul, sub_smul, mul_comm γ]; abel
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hne : ‖(b + (γ * c') • p) - (u + (γ * g (ys t) ⟪u, p⟫) • p)‖ ≤ ‖b - u‖ :=
      cmp_sample_nonexp hγ0 p (by nlinarith [hψ (xs t)]) (hys t) b u
    have hcc : |c - c'| ≤ 16 * (η * T) * n / 4 :=
      (cmp_g_lip (hys t) _ _).trans (by linarith)
    have hc : |c| ≤ 1 := cmp_abs_g_le_one (hys' t) _
    have hres2 : ‖γ • ((c - c') • p + c • (q - p))‖ ≤ γ * K := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
      refine mul_le_mul_of_nonneg_left ?_ hγ0
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |c - c'| * ‖p‖ ≤ 16 * (η * T) * n / 4 * (3 / 4) :=
        mul_le_mul hcc hp (norm_nonneg _) (by positivity)
      have h2 : |c| * ‖q - p‖ ≤ 1 * (4 * (η * T) * n / Real.sqrt m) :=
        mul_le_mul hc hpsi (norm_nonneg _) zero_le_one
      rw [hK]; linarith
    push_cast
    nlinarith

/-- Score comparison through gate changes (`lem:score`). -/
theorem score_comparison {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 < η)
    (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2)
    (θ0 : Params n m) (hG : Good θ0.1) (ha : ‖θ0.2‖ ≤ 2)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, ys t = 1 ∨ ys t = -1)
    (t : ℕ) (ht : t ≤ T) (x : Cube n) :
    |score (traj η θ0 xs ys t) x -
        ⟪frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2) t, psi θ0.1 x⟫| ≤ kappa n m := by
  have hψ : ∀ x, ‖psi θ0.1 x‖ ^ 2 ≤ 9 / 16 := fun x => (hG x).2
  have hys' : ∀ t, |ys t| ≤ 1 := fun t => by rcases hys t with h | h <;> simp [h]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : 576 * (n : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨-, -, hres⟩ := cmp_residuals hn hm hη.le hB θ0 hψ ha xs ys hys' t ht x
  have hgap := cmp_frozen_gap hn hm hη.le hB hγ θ0 hψ ha xs ys hys t ht
  set b := Real.sqrt m • (traj η θ0 xs ys t).2
  set u := frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2) t
  have hp : ‖psi θ0.1 x‖ ≤ 3 / 4 := by nlinarith [hψ x, norm_nonneg (psi θ0.1 x)]
  have hsplit : score (traj η θ0 xs ys t) x - ⟪u, psi θ0.1 x⟫ =
      (score (traj η θ0 xs ys t) x - ⟪b, psi θ0.1 x⟫) + ⟪b - u, psi θ0.1 x⟫ := by
    rw [inner_sub_left]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |⟪b - u, psi θ0.1 x⟫| ≤ ‖b - u‖ * (3 / 4) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hK : 0 ≤ 3 / 16 * (16 * (η * T) * n) + 4 * (η * T) * n / Real.sqrt m := by positivity
  have h2 : (t : ℝ) * (η * m) * (3 / 16 * (16 * (η * T) * n) + 4 * (η * T) * n / Real.sqrt m) ≤
      (η * T) * m * (3 / 16 * (16 * (η * T) * n) + 4 * (η * T) * n / Real.sqrt m) := by
    have : (t : ℝ) * (η * m) ≤ (η * T) * m := by
      nlinarith [mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) m)]
    exact mul_le_mul_of_nonneg_right this hK
  have h3 := cmp_final_arith hnR hmR (mul_nonneg hη.le (Nat.cast_nonneg T))
    (by linarith [show η * T * m = η * m * T by ring])
  unfold kappa
  nlinarith

/-- Score comparison through gate changes (`lem:score`), tail-averaged form. -/
theorem tail_score_comparison {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 < η)
    (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2)
    (θ0 : Params n m) (hG : Good θ0.1) (ha : ‖θ0.2‖ ≤ 2)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, ys t = 1 ∨ ys t = -1) (x : Cube n) :
    |tailScore η T θ0 xs ys x -
        ⟪tailAvg T (frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2)), psi θ0.1 x⟫|
      ≤ kappa n m := by
  have hq : (0 : ℝ) < (tail T).card := by
    have : T ∈ tail T := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    exact_mod_cast Finset.card_pos.mpr ⟨T, this⟩
  unfold tailScore tailAvg
  rw [inner_smul_left, conj_trivial, sum_inner, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_pos (inv_pos.mpr hq)]
  rw [inv_mul_le_iff₀ hq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ t ∈ tail T, |score (traj η θ0 xs ys t) x -
        ⟪frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2) t, psi θ0.1 x⟫|
      ≤ ∑ _t ∈ tail T, kappa n m := Finset.sum_le_sum fun t htl =>
        score_comparison hn hm hη hB hγ θ0 hG ha xs ys hys t (Finset.mem_Icc.mp htl).2 x
    _ = (tail T).card * kappa n m := by rw [Finset.sum_const, nsmul_eq_mul]

end GaussianSGD
