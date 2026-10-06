import GaussianSGD.Init

/-!
# The Gaussian ReLU kernel

The feature map `Φ(x) = ReLU⟪·, x⟫` in `L²(N(0, I_n/n))`, its norm, the identification of
`A_D(h)` with `‖E_D h(x) Φ(x)‖`, and the initialization identity
`E_{W₀} ‖μ‖² = A_D(h)²` from the proof of `thm:risk`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

private lemma abs_relu_le (z : ℝ) : |relu z| ≤ |z| := by
  rcases le_total 0 z with hz | hz
  · simp [relu, max_eq_left hz]
  · simp [relu, max_eq_right hz]

private lemma memLp_relu_gaussianReal (v : NNReal) : MemLp relu 2 (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' 2 (by norm_num)).of_le InitAux.continuous_relu.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using abs_relu_le z)

theorem memLp_relu_inner {n : ℕ} (x : Cube n) :
    MemLp (fun w : Vec n => relu ⟪w, pt x⟫) 2 (rowLaw n) := by
  have h := memLp_relu_gaussianReal (‖pt x‖ ^ 2 / n).toNNReal
  rw [← InitAux.rowLaw_map_inner, memLp_map_measure_iff
    InitAux.continuous_relu.aestronglyMeasurable (by fun_prop)] at h
  exact h

/-- The feature `Φ(x) ∈ L²(N(0, I_n/n))`. -/
def Phi {n : ℕ} (x : Cube n) : Lp ℝ 2 (rowLaw n) := (memLp_relu_inner x).toLp _

/-- In `L²`, the squared norm is the integral of the square. -/
private lemma Lp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : Lp ℝ 2 μ) :
    ‖F‖ ^ 2 = ∫ a, F a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp

private lemma integral_sq_gaussianReal : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

private lemma integral_relu_sq_gaussianReal : ∫ z, relu z ^ 2 ∂(gaussianReal 0 1) = 1 / 2 := by
  have hint : Integrable (fun z => relu z ^ 2) (gaussianReal 0 1) :=
    (memLp_relu_gaussianReal 1).integrable_sq
  have hneg : ∫ z, relu (-z) ^ 2 ∂(gaussianReal 0 1) = ∫ z, relu z ^ 2 ∂(gaussianReal 0 1) := by
    have hm : AEStronglyMeasurable (fun z => relu z ^ 2) ((gaussianReal 0 1).map (fun x => -x)) :=
      (InitAux.continuous_relu.pow 2).aestronglyMeasurable
    rw [← integral_map measurable_neg.aemeasurable hm, gaussianReal_map_neg, neg_zero]
  have hint' : Integrable (fun z => relu (-z) ^ 2) (gaussianReal 0 1) := by
    have hm : AEStronglyMeasurable (fun z => relu z ^ 2) ((gaussianReal 0 1).map (fun x => -x)) :=
      (InitAux.continuous_relu.pow 2).aestronglyMeasurable
    have := (integrable_map_measure hm measurable_neg.aemeasurable).1
      (by rw [gaussianReal_map_neg, neg_zero]; exact hint)
    exact this
  have hsum : ∀ z : ℝ, relu z ^ 2 + relu (-z) ^ 2 = z ^ 2 := by
    intro z
    rcases le_total 0 z with hz | hz
    · simp [relu, max_eq_left hz, max_eq_right (neg_nonpos.2 hz)]
    · simp [relu, max_eq_right hz, max_eq_left (neg_nonneg.2 hz)]
  have h := integral_add hint hint'
  simp_rw [hsum, integral_sq_gaussianReal, hneg] at h
  linarith

private lemma integral_relu_inner_sq {n : ℕ} (hn : 1 ≤ n) (x : Cube n) :
    ∫ w, relu ⟪w, pt x⟫ ^ 2 ∂(rowLaw n) = 1 / 2 := by
  rw [← integral_relu_sq_gaussianReal, ← InitAux.rowLaw_map_inner_pt hn x,
    integral_map (f := fun z => relu z ^ 2) (by fun_prop)
      (InitAux.continuous_relu.pow 2).aestronglyMeasurable]

/-- `‖Φ(x)‖² = 1/2` at every cube point. -/
theorem Phi_norm_sq {n : ℕ} (hn : 1 ≤ n) (x : Cube n) : ‖Phi x‖ ^ 2 = 1 / 2 := by
  rw [Lp_norm_sq, ← integral_relu_inner_sq hn x]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_relu_inner x).coeFn_toLp] with w hw
  rw [Phi, hw]

/-- Finite combinations `∑_x c(x) ReLU⟪w, x⟫` are in `L²`. -/
private lemma memLp_comb {n : ℕ} (c : Cube n → ℝ) :
    MemLp (fun w : Vec n => ∑ x, c x * relu ⟪w, pt x⟫) 2 (rowLaw n) :=
  memLp_finsetSum _ fun x _ => (memLp_relu_inner x).const_mul (c x)

/-- `A_D(h) = ‖E_D h(x) Φ(x)‖`. -/
theorem kernelCorr_eq_norm {n : ℕ} (h : Cube n → Bool) (D : Dist n) :
    kernelCorr h D = ‖∑ x, (D.p x * bsign (h x)) • Phi x‖ := by
  set F : Lp ℝ 2 (rowLaw n) := ∑ x, (D.p x * bsign (h x)) • Phi x
  have hF : ⇑F =ᵐ[rowLaw n] fun w => ∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫ := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun x => (D.p x * bsign (h x)) • Phi x),
      ae_all_iff.2 fun x => Lp.coeFn_smul (D.p x * bsign (h x)) (Phi x),
      ae_all_iff.2 fun x => (memLp_relu_inner x).coeFn_toLp] with w h1 h2 h3
    rw [h1]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [h2 x, Pi.smul_apply, smul_eq_mul, Phi, h3 x]
  rw [kernelCorr, ← Real.sqrt_sq (norm_nonneg F), Lp_norm_sq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hF] with w hw
  rw [hw]

/-- `‖μ‖² = m⁻¹ ∑_j (E_D h(x) ReLU⟪W_j, x⟫)²`. -/
private lemma norm_mu_sq {n m : ℕ} (W : Fin m → Vec n) (h : Cube n → Bool) (D : Dist n) :
    ‖mu (psi W) h D‖ ^ 2 =
      (m : ℝ)⁻¹ * ∑ j, (∑ x, D.p x * bsign (h x) * relu ⟪W j, pt x⟫) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mu, psi, hid, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  have : ∀ x, D.p x * bsign (h x) * ((Real.sqrt m)⁻¹ * relu ⟪W j, pt x⟫) =
      (Real.sqrt m)⁻¹ * (D.p x * bsign (h x) * relu ⟪W j, pt x⟫) := fun x => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

private lemma integrable_row_sq {n m : ℕ} (c : Cube n → ℝ) (j : Fin m) :
    Integrable (fun W : Fin m → Vec n => (∑ x, c x * relu ⟪W j, pt x⟫) ^ 2) (hiddenLaw n m) :=
  integrable_comp_eval (μ := fun _ : Fin m => rowLaw n)
    (f := fun w : Vec n => (∑ x, c x * relu ⟪w, pt x⟫) ^ 2) (memLp_comb c).integrable_sq

private lemma integrable_norm_mu_sq {n m : ℕ} (h : Cube n → Bool) (D : Dist n) :
    Integrable (fun W => ‖mu (psi W) h D‖ ^ 2) (hiddenLaw n m) := by
  simp_rw [norm_mu_sq]
  exact (integrable_finsetSum _ fun j _ => integrable_row_sq _ j).const_mul _

/-- The initialization identity `E_{W₀} ‖μ‖² = A_D(h)²`. -/
theorem kernel_identity {n m : ℕ} (_hn : 1 ≤ n) (hm : 1 ≤ m) (h : Cube n → Bool) (D : Dist n) :
    ∫ W, ‖mu (psi W) h D‖ ^ 2 ∂(hiddenLaw n m) = kernelCorr h D ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  simp_rw [norm_mu_sq]
  rw [integral_const_mul, integral_finsetSum _ fun j _ => integrable_row_sq _ j]
  have hrow : ∀ j : Fin m, ∫ W, (∑ x, D.p x * bsign (h x) * relu ⟪W j, pt x⟫) ^ 2 ∂(hiddenLaw n m)
      = ∫ w, (∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫) ^ 2 ∂(rowLaw n) := fun j =>
    integral_comp_eval (μ := fun _ : Fin m => rowLaw n)
      (f := fun w : Vec n => (∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫) ^ 2)
      (memLp_comb _).integrable_sq.aestronglyMeasurable
  simp_rw [hrow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hm', one_mul, kernelCorr,
    Real.sq_sqrt (integral_nonneg fun w => sq_nonneg _)]

theorem integrable_norm_mu {n m : ℕ} (h : Cube n → Bool) (D : Dist n) :
    Integrable (fun W => ‖mu (psi W) h D‖) (hiddenLaw n m) := by
  have hmeas : AEStronglyMeasurable (fun W : Fin m → Vec n => ‖mu (psi W) h D‖) (hiddenLaw n m) := by
    have hc : Continuous fun W : Fin m → Vec n => mu (psi W) h D := by
      have := InitAux.continuous_relu
      unfold mu psi hid
      fun_prop
    exact hc.norm.aestronglyMeasurable
  exact ((memLp_two_iff_integrable_sq hmeas).2 (integrable_norm_mu_sq h D)).integrable one_le_two

/-- The character `χ_B(x) = ∏_{i ∈ B} x_i`. -/
private def chi {n : ℕ} (B : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ B, bsign (x i)

private lemma bsign_parity {n : ℕ} (A : Finset (Fin n)) (x : Cube n) :
    bsign (parity A x) = chi A x := by
  have h : chi A x = 1 ∨ chi A x = -1 := by
    unfold chi
    refine Finset.prod_induction _ (fun r => r = 1 ∨ r = -1) ?_ (Or.inl rfl) ?_
    · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
    · intro i _; cases x i <;> simp [bsign]
  have hp : parity A x = decide (chi A x = 1) := rfl
  rcases h with h | h
  · simp [hp, h, bsign]
  · rw [hp, h]; norm_num [bsign]

/-- Parseval's identity on the cube, in the form needed here. -/
private lemma sum_sq_fourier {n : ℕ} (f : Cube n → ℝ) :
    ∑ B : Finset (Fin n), (∑ x, (1 / 2 ^ n : ℝ) * chi B x * f x) ^ 2 =
      (1 / 2 ^ n : ℝ) * ∑ x, f x ^ 2 := by
  have hchar : ∀ x y : Cube n, ∑ B : Finset (Fin n), chi B x * chi B y =
      if x = y then (2 : ℝ) ^ n else 0 := by
    intro x y
    have h1 : ∀ B : Finset (Fin n), chi B x * chi B y = ∏ i ∈ B, (bsign (x i) * bsign (y i)) := by
      intro B; simp [chi, Finset.prod_mul_distrib]
    simp_rw [h1]
    rw [← Finset.powerset_univ, ← Finset.prod_one_add]
    split_ifs with hxy
    · subst hxy
      have : ∀ i, 1 + bsign (x i) * bsign (x i) = 2 := by
        intro i; cases x i <;> norm_num [bsign]
      simp [this]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      cases hx : x i <;> cases hy : y i <;> simp_all [bsign]
  calc ∑ B : Finset (Fin n), (∑ x, (1 / 2 ^ n : ℝ) * chi B x * f x) ^ 2
      = ∑ B : Finset (Fin n), ∑ x, ∑ y,
          (1 / 2 ^ n : ℝ) ^ 2 * f x * f y * (chi B x * chi B y) := by
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = ∑ x, ∑ y, (1 / 2 ^ n : ℝ) ^ 2 * f x * f y * ∑ B : Finset (Fin n), chi B x * chi B y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = (1 / 2 ^ n : ℝ) * ∑ x, f x ^ 2 := by
        simp_rw [hchar, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        field_simp

/-- Coordinate permutation `w ↦ w ∘ τ` as a linear isometry. -/
private def permIso {n : ℕ} (τ : Equiv.Perm (Fin n)) : Vec n ≃ₗᵢ[ℝ] Vec n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ τ.symm

private lemma permIso_apply {n : ℕ} (τ : Equiv.Perm (Fin n)) (w : Vec n) (i : Fin n) :
    (permIso τ w) i = w (τ i) := by
  simp [permIso]

private lemma rowLaw_map_permIso {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    (rowLaw n).map (permIso τ) = rowLaw n := by
  have hcomm : (permIso τ) ∘ (fun u : Vec n => (Real.sqrt n)⁻¹ • u) =
      (fun u : Vec n => (Real.sqrt n)⁻¹ • u) ∘ (permIso τ) := by
    funext u; simp
  rw [rowLaw, Measure.map_map (by fun_prop) (by fun_prop), hcomm,
    ← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map]

private lemma inner_permIso_pt {n : ℕ} (τ : Equiv.Perm (Fin n)) (w : Vec n) (y : Cube n) :
    ⟪permIso τ w, pt (y ∘ τ)⟫ = ⟪w, pt y⟫ := by
  simp only [PiLp.inner_apply, permIso_apply, pt]
  exact Equiv.sum_comp τ (fun i => ⟪w.ofLp i, bsign (y i)⟫)

/-- Any two index sets of equal size differ by a coordinate permutation. -/
private lemma exists_perm_map_eq {n : ℕ} {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ τ : Equiv.Perm (Fin n), A.map τ.toEmbedding = B := by
  classical
  have e : {i // i ∈ A} ≃ {i // i ∈ B} := Fintype.equivOfCardEq (by simpa using h)
  have f : {i // i ∉ A} ≃ {i // i ∉ B} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨Equiv.subtypeCongr e f, ?_⟩
  refine Finset.eq_of_subset_of_card_le ?_ (by simp [h])
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
  simp [Equiv.subtypeCongr, hi]

/-- Reindexing of the cube by a coordinate permutation, `y ↦ y ∘ τ`. -/
private def cubePerm {n : ℕ} (τ : Equiv.Perm (Fin n)) : Cube n ≃ Cube n where
  toFun y := y ∘ τ
  invFun x := x ∘ τ.symm
  left_inv y := by funext i; simp
  right_inv x := by funext i; simp

/-- `λ_B = E_w (E_x χ_B(x) ReLU⟪w, x⟫)²` under the uniform marginal. -/
private def lam {n : ℕ} (B : Finset (Fin n)) : ℝ :=
  ∫ w, (∑ x, (1 / 2 ^ n : ℝ) * chi B x * relu ⟪w, pt x⟫) ^ 2 ∂(rowLaw n)

/-- `λ_B` is invariant under coordinate permutations. -/
private lemma lam_map_perm {n : ℕ} (τ : Equiv.Perm (Fin n)) (B : Finset (Fin n)) :
    lam (B.map τ.toEmbedding) = lam B := by
  have hpt : ∀ w : Vec n, ∑ x, (1 / 2 ^ n : ℝ) * chi (B.map τ.toEmbedding) x * relu ⟪w, pt x⟫ =
      ∑ x, (1 / 2 ^ n : ℝ) * chi B x * relu ⟪permIso τ w, pt x⟫ := by
    intro w
    rw [← Equiv.sum_comp (cubePerm τ) (fun x => (1 / 2 ^ n : ℝ) * chi B x *
      relu ⟪permIso τ w, pt x⟫)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h1 : chi B (cubePerm τ y) = chi (B.map τ.toEmbedding) y := by
      simp [chi, cubePerm, Finset.prod_map]
    have h2 : ⟪permIso τ w, pt (cubePerm τ y)⟫ = ⟪w, pt y⟫ := inner_permIso_pt τ w y
    rw [h1, h2]
  have hg : Continuous fun w : Vec n => (∑ x, (1 / 2 ^ n : ℝ) * chi B x * relu ⟪w, pt x⟫) ^ 2 := by
    have := InitAux.continuous_relu
    fun_prop
  unfold lam
  simp_rw [hpt]
  have h := integral_map (μ := rowLaw n) (φ := permIso τ)
    (f := fun w : Vec n => (∑ x, (1 / 2 ^ n : ℝ) * chi B x * relu ⟪w, pt x⟫) ^ 2) (by fun_prop)
    (by rw [rowLaw_map_permIso]; exact hg.aestronglyMeasurable)
  rw [rowLaw_map_permIso] at h
  exact h.symm

/-- Parity bound from the proof of `cor:parity`: under the uniform marginal,
`A(χ_A)² = λ_k ≤ 1 / (2 (n choose k))` with `k = |A|`. -/
theorem kernelCorr_parity_sq_le {n : ℕ} (hn : 1 ≤ n) (A : Finset (Fin n)) :
    kernelCorr (parity A) (unif n) ^ 2 ≤ 1 / (2 * (n.choose A.card)) := by
  have hkA : kernelCorr (parity A) (unif n) ^ 2 = lam A := by
    rw [kernelCorr, Real.sq_sqrt (integral_nonneg fun w => sq_nonneg _)]
    simp [unif, bsign_parity, lam]
  have hint : ∀ B : Finset (Fin n),
      Integrable (fun w => (∑ x, (1 / 2 ^ n : ℝ) * chi B x * relu ⟪w, pt x⟫) ^ 2) (rowLaw n) :=
    fun B => (memLp_comb fun x => (1 / 2 ^ n : ℝ) * chi B x).integrable_sq
  have hsum : ∑ B : Finset (Fin n), lam B = 1 / 2 := by
    unfold lam
    rw [← integral_finsetSum _ fun B _ => hint B]
    simp_rw [sum_sq_fourier]
    rw [integral_const_mul, integral_finsetSum _ fun x _ => (memLp_relu_inner x).integrable_sq]
    simp_rw [integral_relu_inner_sq hn]
    simp
  have hperm : ∀ B ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), lam B = lam A := by
    intro B hB
    obtain ⟨τ, hτ⟩ := exists_perm_map_eq (Finset.mem_powersetCard.1 hB).2.symm
    rw [← hτ, lam_map_perm]
  have hchoose : (n.choose A.card : ℝ) * lam A ≤ 1 / 2 := by
    calc (n.choose A.card : ℝ) * lam A
        = ∑ B ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), lam B := by
          rw [Finset.sum_congr rfl hperm, Finset.sum_const, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ B : Finset (Fin n), lam B :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun B _ _ => integral_nonneg fun w => sq_nonneg _
      _ = 1 / 2 := hsum
  have hpos : (0 : ℝ) < n.choose A.card := by
    have := A.card_le_univ
    rw [Fintype.card_fin] at this
    exact_mod_cast Nat.choose_pos this
  rw [hkA, le_div_iff₀ (by positivity)]
  linarith

end GaussianSGD
