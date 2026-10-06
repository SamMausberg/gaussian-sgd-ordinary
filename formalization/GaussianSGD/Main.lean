import GaussianSGD.Risk
import GaussianSGD.Geometry

/-!
# Kernel margin from success under every marginal (`thm:margin`) and corollaries

All-marginal success forces a Gaussian ReLU kernel margin and bounds the VC
dimension. The section also records the explicit sufficient conditions on
`m` and `T`, the numerical instance `m ≥ 2^20 n`, `T ≥ 2^24`, and the parity bound.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace RiskAux

lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hx (by linarith [Real.add_one_le_exp x])

lemma sq_le_exp {y : ℝ} (hy : 0 ≤ y) : (1 + y / 2) ^ 2 ≤ Real.exp y := by
  have h := Real.add_one_le_exp (y / 2)
  have h2 : Real.exp y = Real.exp (y / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h2]
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- `ρ_W ≤ 4 e^{-y}` once `m/16384 ≥ n y` and `2 e^{-y} ≤ 1`, using `n ≥ 1`. -/
lemma rhoW_le {n m : ℕ} (hn : 1 ≤ n) {y : ℝ} (hm : n * y ≤ m / 16384)
    (h2 : 2 * Real.exp (-y) ≤ 1) : rhoW n m ≤ 4 * Real.exp (-y) := by
  refine (min_le_right _ _).trans ?_
  have h1 : Real.exp (-(m : ℝ) / 16384) ≤ Real.exp (-y) ^ n := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by linarith [neg_div 16384 (m : ℝ)])
  have hpow : (2 * Real.exp (-y)) ^ n ≤ 2 * Real.exp (-y) :=
    pow_le_of_le_one (by positivity) h2 (by omega)
  calc (2 : ℝ) ^ (n + 1) * Real.exp (-(m : ℝ) / 16384)
      ≤ 2 ^ (n + 1) * Real.exp (-y) ^ n := by gcongr
    _ = 2 * (2 * Real.exp (-y)) ^ n := by rw [mul_pow, pow_succ]; ring
    _ ≤ 2 * (2 * Real.exp (-y)) := by gcongr
    _ = 4 * Real.exp (-y) := by ring

end RiskAux

/-- Kernel margin from success under every marginal (`thm:margin`): margin and VC parts. -/
theorem kernel_margin {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (H : Finset (Cube n → Bool))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε)
    (hΔ : lossTerm n m T (η * m * T) ≤ (1 / 2 - ε) / 2) :
    (∀ h ∈ H, ∀ D : Dist n, (1 / 2 - ε) / (18 * (η * m * T)) ≤ kernelCorr h D) ∧
    (∀ h ∈ H, ∃ u : Lp ℝ 2 (rowLaw n), ‖u‖ = 1 ∧
        ∀ x, (1 / 2 - ε) / (18 * (η * m * T)) ≤ bsign (h x) * ⟪u, Phi x⟫) ∧
    (∀ S : Finset (Cube n), Shatters H S →
        (S.card : ℝ) ≤ 162 * (η * m * T) ^ 2 / (1 / 2 - ε) ^ 2) := by
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hBpos : 0 < η * m * T := by positivity
  have hθ : 0 < 1 / 2 - ε := by linarith
  have hA : ∀ h ∈ H, ∀ D : Dist n, (1 / 2 - ε) / (18 * (η * m * T)) ≤ kernelCorr h D := by
    intro h hh D
    have h1 := (risk_lower_bound hn hm hT hη hB hγ h D).trans (hprem h hh D)
    rw [ENNReal.ofReal_le_ofReal_iff hε0] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hc : 0 < (1 / 2 - ε) / (18 * (η * m * T)) := by positivity
  have hall : ∀ h ∈ H, ∀ p : Cube n → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      (1 / 2 - ε) / (18 * (η * m * T)) ≤ ‖∑ x, (p x * bsign (h x)) • Phi x‖ := by
    intro h hh p hp hp1
    have := hA h hh ⟨p, hp, hp1⟩
    rwa [kernelCorr_eq_norm] at this
  obtain ⟨hmarg, hvc⟩ := margin_and_vc Phi (fun x => (Phi_norm_sq hn x).le) H hc hall
  refine ⟨hA, hmarg, fun S hS => (hvc S hS).trans_eq ?_⟩
  field_simp
  ring

/-- Explicit sufficient conditions for `Δ ≤ θ/2` (`thm:margin`). -/
theorem lossTerm_le_half {n m T : ℕ} (hn : 1 ≤ n) {B θ : ℝ} (hB : 0 < B) (hθ0 : 0 < θ)
    (hθ : θ ≤ 1 / 2) (hm : 2 ^ 17 * (n : ℝ) / θ ≤ m) (hT : (216 * B / θ) ^ 2 ≤ T) :
    lossTerm n m T B ≤ θ / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : 2 ^ 17 * (n : ℝ) ≤ m * θ := (div_le_iff₀ hθ0).1 hm
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  set y := 8 / θ with hy
  have hy16 : 16 ≤ y := by rw [hy, le_div_iff₀ hθ0]; linarith
  have hyθ : y * θ = 8 := by rw [hy]; field_simp
  have hexp : Real.exp (-y) ≤ (2 * y)⁻¹ := by
    rw [Real.exp_neg]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [RiskAux.sq_le_exp (show 0 ≤ y by linarith)]
  -- Each of the four terms of `Δ` is at most `θ/8`.
  have hW : rhoW n m ≤ θ / 4 := by
    have hny : n * y ≤ m / 16384 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h2 : 2 * Real.exp (-y) ≤ 1 := by
      calc 2 * Real.exp (-y) ≤ 2 * (2 * y)⁻¹ := by gcongr
        _ ≤ 1 := by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul];
                    exact inv_le_one_of_one_le₀ (by linarith)
    refine (RiskAux.rhoW_le hn hny h2).trans ?_
    calc 4 * Real.exp (-y) ≤ 4 * (2 * y)⁻¹ := by gcongr
      _ = θ / 4 := by rw [hy]; field_simp; ring
  have ha : rhoA m ≤ θ / 8 := by
    unfold rhoA
    rw [neg_div]
    refine (RiskAux.exp_neg_le_inv (by positivity)).trans ?_
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  have hk : 24 * kappa n m ≤ θ / 8 := by
    unfold kappa
    rw [mul_div_assoc', div_le_iff₀ hmpos]
    nlinarith
  have hsq : 216 * B / θ ≤ Real.sqrt T := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 216 * B / θ)]
    exact Real.sqrt_le_sqrt hT
  have hsqpos : 0 < 216 * B / θ := by positivity
  have hTt : 27 * B / Real.sqrt T ≤ θ / 8 := by
    calc 27 * B / Real.sqrt T ≤ 27 * B / (216 * B / θ) :=
          div_le_div_of_nonneg_left (by positivity) hsqpos hsq
      _ = θ / 8 := by field_simp; ring
  unfold lossTerm
  linarith

/-- The conditions `m ≥ 2^17 n/θ` and `T ≥ (216B/θ)²` of `thm:margin` also give
`m ≥ 576 n` and `γ = B/T ≤ 1/2`. -/
theorem regime_of_large {n m T : ℕ} (hn : 1 ≤ n) {B θ : ℝ} (hB : 0 < B)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hm : 2 ^ 17 * (n : ℝ) / θ ≤ m)
    (hT : (216 * B / θ) ^ 2 ≤ T) :
    576 * n ≤ m ∧ B / T ≤ 1 / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (1 : ℝ) ≤ T := by
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hT0)
  refine ⟨?_, ?_⟩
  · have h1 : (2 : ℝ) ^ 18 * n ≤ 2 ^ 17 * n / θ := by
      rw [le_div_iff₀ hθ0]; nlinarith
    have : (576 : ℝ) * n ≤ m := by nlinarith
    exact_mod_cast this
  · rw [div_le_iff₀ (by linarith)]
    by_cases h2 : 2 * B ≤ 1
    · linarith
    · have h432 : 432 * B ≤ 216 * B / θ := by
        rw [le_div_iff₀ hθ0]; nlinarith
      have hsq : (432 * B) ^ 2 ≤ (216 * B / θ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h432 2
      nlinarith

/-- The numerical instance: `m ≥ 2^20 n`, `T ≥ 2^24`, `B ≤ 12` give `Δ ≤ 471/4096 < 1/8`. -/
theorem lossTerm_regime {n m T : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB0 : 0 < B) (hB : B ≤ 12)
    (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T) :
    lossTerm n m T B ≤ 471 / 4096 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ^ 20 * n ≤ m := by exact_mod_cast hm
  have hTR : (2 : ℝ) ^ 24 ≤ T := by exact_mod_cast hT
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
  have hexp : Real.exp (-64) ≤ 1 / 1089 := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (by norm_num) ?_
    have := RiskAux.sq_le_exp (show (0 : ℝ) ≤ 64 by norm_num)
    norm_num at this
    linarith
  have hW : rhoW n m ≤ 1 / 64 := by
    have hny : n * (64 : ℝ) ≤ m / 16384 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    refine (RiskAux.rhoW_le hn hny (by linarith)).trans ?_
    linarith
  have ha : rhoA m ≤ 1 / 64 := by
    unfold rhoA
    rw [neg_div]
    refine (RiskAux.exp_neg_le_inv (by positivity)).trans ?_
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  have hk : 24 * kappa n m ≤ 51 / 4096 := by
    unfold kappa
    rw [mul_div_assoc', div_le_iff₀ hmpos]
    nlinarith
  have hsq : (4096 : ℝ) ≤ Real.sqrt T := by
    rw [show (4096 : ℝ) = Real.sqrt (2 ^ 24) by
      rw [show (2 : ℝ) ^ 24 = 4096 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hTR
  have hTt : 27 * B / Real.sqrt T ≤ 324 / 4096 := by
    calc 27 * B / Real.sqrt T ≤ 27 * B / 4096 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
      _ ≤ 324 / 4096 := by linarith
  unfold lossTerm
  linarith

/-- `thm:risk` in the numerical regime: `Risk(h,D) ≥ 3/8 - 9 B A_D(h)`. -/
theorem risk_lower_bound_regime {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m)
    (hT : 2 ^ 24 ≤ T) {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (h : Cube n → Bool)
    (D : Dist n) :
    ENNReal.ofReal (3 / 8 - 9 * (η * m * T) * kernelCorr h D) ≤ risk m η T h D := by
  have hm' : 576 * n ≤ m := le_trans (Nat.mul_le_mul_right n (by norm_num)) hm
  have hT' : 1 ≤ T := le_trans (by norm_num) hT
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hTR : (2 : ℝ) ^ 24 ≤ T := by exact_mod_cast hT
  have hγ0 : 0 < η * m := by positivity
  have hγ : η * m ≤ 1 / 2 := by nlinarith
  have hBpos : 0 < η * m * T := by positivity
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (risk_lower_bound hn hm' hT' hη hB hγ h D)
  linarith [lossTerm_regime hn hBpos hB hm hT]

/-- `thm:margin` in the numerical regime with error below `1/4`: margin `1/(72B)` and
`VC(H) ≤ 2592 B²`. -/
theorem kernel_margin_regime {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T)
    {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (H : Finset (Cube n → Bool)) {ε : ℝ}
    (hε : ε < 1 / 4) (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε) :
    (∀ h ∈ H, ∃ u : Lp ℝ 2 (rowLaw n), ‖u‖ = 1 ∧
        ∀ x, 1 / (72 * (η * m * T)) ≤ bsign (h x) * ⟪u, Phi x⟫) ∧
    (∀ S : Finset (Cube n), Shatters H S → (S.card : ℝ) ≤ 2592 * (η * m * T) ^ 2) := by
  have hm' : 576 * n ≤ m := le_trans (Nat.mul_le_mul_right n (by norm_num)) hm
  have hT' : 1 ≤ T := le_trans (by norm_num) hT
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hTR : (2 : ℝ) ^ 24 ≤ T := by exact_mod_cast hT
  have hγ0 : 0 < η * m := by positivity
  have hγ : η * m ≤ 1 / 2 := by nlinarith
  have hBpos : 0 < η * m * T := by positivity
  set ε' := max ε 0 with hε'
  have hε'0 : 0 ≤ ε' := le_max_right _ _
  have hε'4 : ε' < 1 / 4 := max_lt hε (by norm_num)
  have hprem' : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε' := fun h hh D =>
    (hprem h hh D).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hΔ : lossTerm n m T (η * m * T) ≤ (1 / 2 - ε') / 2 := by
    linarith [lossTerm_regime hn hBpos hB hm hT]
  obtain ⟨-, hmarg, hvc⟩ :=
    kernel_margin hn hm' hT' hη hB hγ H hε'0 (by linarith) hprem' hΔ
  have hθ : 1 / 4 < 1 / 2 - ε' := by linarith
  refine ⟨fun h hh => ?_, fun S hS => (hvc S hS).trans ?_⟩
  · obtain ⟨u, hu, hux⟩ := hmarg h hh
    refine ⟨u, hu, fun x => le_trans ?_ (hux x)⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : (1 / 4 : ℝ) ^ 2 ≤ (1 / 2 - ε') ^ 2 := pow_le_pow_left₀ (by norm_num) hθ.le 2
    nlinarith [sq_nonneg (η * m * T)]

/-- Parity obstruction (`cor:parity`). -/
theorem parity_lower_bound {n m T : ℕ} (hn : 1 ≤ n) (hm : 2 ^ 20 * n ≤ m) (hT : 2 ^ 24 ≤ T)
    {η : ℝ} (hη : 0 < η) (hB : η * m * T ≤ 12) (A : Finset (Fin n)) :
    ENNReal.ofReal (3 / 8 - 9 * (η * m * T) / Real.sqrt (2 * (n.choose A.card)))
      ≤ risk m η T (parity A) (unif n) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (risk_lower_bound_regime hn hm hT hη hB _ _)
  have hA : kernelCorr (parity A) (unif n) ≤ (Real.sqrt (2 * (n.choose A.card)))⁻¹ := by
    rw [← Real.sqrt_inv, ← one_div]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt (kernelCorr_parity_sq_le hn A))
  have hBnn : 0 ≤ η * m * T := by positivity
  have h2 : 9 * (η * m * T) * kernelCorr (parity A) (unif n)
      ≤ 9 * (η * m * T) / Real.sqrt (2 * (n.choose A.card)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

end GaussianSGD
