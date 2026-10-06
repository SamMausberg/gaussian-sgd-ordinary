import GaussianSGD.Main

/-!
# Adjacent points (`cor:edge`)

A target that is not constant differs at two adjacent cube points. Under the uniform
distribution on those two points its kernel correlation is at most `1/√n`, so the risk bound of
`thm:risk` leaves almost no room to learn it. Under the hypotheses of `thm:margin` the learned
class is therefore constant once `n > (18B/θ)²`.
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GaussianSGD

namespace EdgeAux

/-- A nonconstant function on the cube changes value along some edge. -/
lemma exists_edge {n : ℕ} (h : Cube n → Bool) (hh : ∃ x y, h x ≠ h y) :
    ∃ (x : Cube n) (i : Fin n), h x ≠ h (Function.update x i (!x i)) := by
  by_contra hcon
  push Not at hcon
  have key : ∀ s : Finset (Fin n), ∀ x y : Cube n, (∀ i, x i ≠ y i → i ∈ s) → h x = h y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y hxy
      congr 1
      funext i
      by_contra hi
      exact absurd (hxy i hi) (Finset.notMem_empty i)
    | insert a s ha ih =>
      intro x y hxy
      by_cases hxa : x a = y a
      · refine ih x y fun i hi => ?_
        rcases Finset.mem_insert.1 (hxy i hi) with rfl | hs
        · exact absurd hxa hi
        · exact hs
      · set x' := Function.update x a (!x a)
        rw [hcon x a]
        refine ih x' y fun i hi => ?_
        by_cases hia : i = a
        · subst hia
          exfalso; apply hi
          simp only [x', Function.update_self]
          cases hx : x i <;> cases hy : y i <;> simp_all
        · rcases Finset.mem_insert.1 (hxy i (by simpa [x', Function.update_of_ne hia] using hi))
            with rfl | hs
          · exact absurd rfl hia
          · exact hs
  obtain ⟨x, y, hxy⟩ := hh
  exact hxy (key Finset.univ x y fun i _ => Finset.mem_univ i)

/-- The distribution giving mass `1/2` to each of two cube points. -/
def pairDist {n : ℕ} (x y : Cube n) : Dist n where
  p z := (if z = x then 1 / 2 else 0) + (if z = y then 1 / 2 else 0)
  nonneg z := by positivity
  sum_one := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num

lemma pairDist_left {n : ℕ} {x y : Cube n} (hxy : x ≠ y) : (pairDist x y).p x = 1 / 2 := by
  simp [pairDist, hxy]

lemma pairDist_right {n : ℕ} {x y : Cube n} (hxy : x ≠ y) : (pairDist x y).p y = 1 / 2 := by
  simp [pairDist, hxy.symm]

/-- `E ⟪w, v⟫² = ‖v‖²/n` for `w ∼ N(0, I_n/n)`. -/
lemma integral_inner_sq_rowLaw {n : ℕ} (v : Vec n) :
    ∫ w, ⟪w, v⟫ ^ 2 ∂(rowLaw n) = ‖v‖ ^ 2 / n := by
  have hm : AEStronglyMeasurable (fun z : ℝ => z ^ 2) ((rowLaw n).map fun w => ⟪w, v⟫) :=
    (continuous_pow 2).aestronglyMeasurable
  rw [← integral_map (f := fun z : ℝ => z ^ 2) (by fun_prop) hm, InitAux.rowLaw_map_inner]
  have h := variance_fun_id_gaussianReal (μ := 0) (v := (‖v‖ ^ 2 / n).toNNReal)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  rw [h, Real.coe_toNNReal _ (by positivity)]

lemma integrable_inner_sq_rowLaw {n : ℕ} (v : Vec n) :
    Integrable (fun w => ⟪w, v⟫ ^ 2) (rowLaw n) := by
  have hm : AEStronglyMeasurable (fun z : ℝ => z ^ 2) ((rowLaw n).map fun w => ⟪w, v⟫) :=
    (continuous_pow 2).aestronglyMeasurable
  have := (integrable_map_measure hm (by fun_prop)).1
    (by rw [InitAux.rowLaw_map_inner]; exact (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq)
  exact this

/-- `ReLU` is `1`-Lipschitz. -/
lemma abs_relu_sub_le (a b : ℝ) : |relu a - relu b| ≤ |a - b| := by
  unfold relu
  exact abs_max_sub_max_le_abs a b 0

/-- Across an edge where the target changes, the kernel correlation is at most `1/√n`. -/
lemma kernelCorr_edge_le {n : ℕ} (h : Cube n → Bool) (x : Cube n) (i : Fin n)
    (hxi : h x ≠ h (Function.update x i (!x i))) :
    kernelCorr h (pairDist x (Function.update x i (!x i))) ≤ 1 / Real.sqrt n := by
  set x' := Function.update x i (!x i)
  set v : Vec n := pt x - pt x'
  have hv : ‖v‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_eq_single i]
    · simp only [v, x', pt, WithLp.ofLp_sub, Pi.sub_apply, Function.update_self]
      cases x i <;> norm_num [bsign]
    · intro j _ hj
      simp [v, x', pt, Function.update_of_ne hj]
    · simp
  have hb : bsign (h x') = -bsign (h x) := by
    cases hx : h x <;> cases hx' : h x' <;> simp_all [bsign]
  have hsum : ∀ w : Vec n, ∑ z, (pairDist x x').p z * bsign (h z) * relu ⟪w, pt z⟫ =
      bsign (h x) / 2 * (relu ⟪w, pt x⟫ - relu ⟪w, pt x'⟫) := by
    intro w
    simp only [pairDist, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hb]
    ring
  have hpt : ∀ w : Vec n, (∑ z, (pairDist x x').p z * bsign (h z) * relu ⟪w, pt z⟫) ^ 2 ≤
      1 / 4 * ⟪w, v⟫ ^ 2 := by
    intro w
    rw [hsum]
    have hbs : bsign (h x) ^ 2 = 1 := by cases h x <;> norm_num [bsign]
    have hl := abs_relu_sub_le ⟪w, pt x⟫ ⟪w, pt x'⟫
    have hl2 : (relu ⟪w, pt x⟫ - relu ⟪w, pt x'⟫) ^ 2 ≤ ⟪w, v⟫ ^ 2 := by
      rw [show ⟪w, v⟫ = ⟪w, pt x⟫ - ⟪w, pt x'⟫ from inner_sub_right _ _ _]
      exact sq_le_sq.2 hl
    calc (bsign (h x) / 2 * (relu ⟪w, pt x⟫ - relu ⟪w, pt x'⟫)) ^ 2
        = 1 / 4 * (relu ⟪w, pt x⟫ - relu ⟪w, pt x'⟫) ^ 2 := by rw [mul_pow, div_pow, hbs]; ring
      _ ≤ 1 / 4 * ⟪w, v⟫ ^ 2 := by gcongr
  have hint : ∫ w, (∑ z, (pairDist x x').p z * bsign (h z) * relu ⟪w, pt z⟫) ^ 2 ∂(rowLaw n)
      ≤ 1 / n := by
    calc _ ≤ ∫ w, 1 / 4 * ⟪w, v⟫ ^ 2 ∂(rowLaw n) :=
          integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _)
            ((integrable_inner_sq_rowLaw v).const_mul _) (ae_of_all _ hpt)
      _ = 1 / n := by
          rw [integral_const_mul, integral_inner_sq_rowLaw, hv]
          ring
  rw [kernelCorr, one_div, ← Real.sqrt_inv, ← one_div]
  exact Real.sqrt_le_sqrt hint

end EdgeAux

open EdgeAux

/-- Adjacent points (`cor:edge`), risk bound: a nonconstant target has a marginal supported on
two adjacent cube points with `Risk(h,D) ≥ 1/2 - Δ - 9B/√n`. -/
theorem edge_lower_bound {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (h : Cube n → Bool)
    (hh : ∃ x y, h x ≠ h y) :
    ∃ (x : Cube n) (i : Fin n) (D : Dist n),
      D.p x = 1 / 2 ∧ D.p (Function.update x i (!x i)) = 1 / 2 ∧
      ENNReal.ofReal (1 / 2 - lossTerm n m T (η * m * T) - 9 * (η * m * T) / Real.sqrt n)
        ≤ risk m η T h D := by
  obtain ⟨x, i, hxi⟩ := exists_edge h hh
  have hne : x ≠ Function.update x i (!x i) := by
    intro he
    have := congrFun he i
    rw [Function.update_self] at this
    cases hx : x i <;> simp [hx] at this
  refine ⟨x, i, pairDist x (Function.update x i (!x i)), pairDist_left hne, pairDist_right hne,
    le_trans (ENNReal.ofReal_le_ofReal ?_) (risk_lower_bound hn hm hT hη hB hγ h _)⟩
  have hBnn : 0 ≤ η * m * T := by positivity
  have hk := kernelCorr_edge_le h x i hxi
  have : 9 * (η * m * T) * kernelCorr h (pairDist x (Function.update x i (!x i))) ≤
      9 * (η * m * T) / Real.sqrt n := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hk (by positivity)
  linarith

/-- Adjacent points (`cor:edge`), consequence: under the hypotheses of `thm:margin`, every
target in the class is constant once `n > (18B/θ)²`. -/
theorem class_constant {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) (hT : 1 ≤ T) {η : ℝ}
    (hη : 0 < η) (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2) (H : Finset (Cube n → Bool))
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    (hprem : ∀ h ∈ H, ∀ D : Dist n, risk m η T h D ≤ ENNReal.ofReal ε)
    (hΔ : lossTerm n m T (η * m * T) ≤ (1 / 2 - ε) / 2)
    (hlarge : (18 * (η * m * T) / (1 / 2 - ε)) ^ 2 < n) :
    ∀ h ∈ H, ∀ x y, h x = h y := by
  intro h hH x y
  by_contra hxy
  obtain ⟨_, _, D, -, -, hD⟩ := edge_lower_bound hn hm hT hη hB hγ h ⟨x, y, hxy⟩
  have hle := (ENNReal.ofReal_le_ofReal_iff hε0).1 (hD.trans (hprem h hH D))
  have hθ : 0 < 1 / 2 - ε := by linarith
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h1 : (1 / 2 - ε) / 2 ≤ 9 * (η * m * T) / Real.sqrt n := by linarith
  have h2 : Real.sqrt n ≤ 18 * (η * m * T) / (1 / 2 - ε) := by
    rw [le_div_iff₀ hθ]
    rw [le_div_iff₀ hsn] at h1
    linarith
  have h3 : (n : ℝ) ≤ (18 * (η * m * T) / (1 / 2 - ε)) ^ 2 := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg n)]
    exact pow_le_pow_left₀ hsn.le h2 2
  linarith

end GaussianSGD
