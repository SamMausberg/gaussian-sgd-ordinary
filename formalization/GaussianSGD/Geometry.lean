import GaussianSGD.Defs

/-!
# Convex separation and the VC bound (`lem:geometry`)
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace GaussianSGD

/-- Some choice of signs makes the squared norm of the signed sum at most the sum of the
squared norms. -/
private lemma exists_signs_norm_sq_le {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {X : Type*} [DecidableEq X] (Φ : X → K) (S : Finset X) :
    ∃ σ : X → Bool, ‖∑ x ∈ S, bsign (σ x) • Φ x‖ ^ 2 ≤ ∑ x ∈ S, ‖Φ x‖ ^ 2 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => true, by simp⟩
  | insert a S ha ih =>
    obtain ⟨σ, hσ⟩ := ih
    set s := ∑ x ∈ S, bsign (σ x) • Φ x
    have hpar : ‖s + Φ a‖ ^ 2 + ‖s - Φ a‖ ^ 2 = 2 * ‖s‖ ^ 2 + 2 * ‖Φ a‖ ^ 2 := by
      rw [@norm_add_sq_real, @norm_sub_sq_real]; ring
    have key : ∀ b : Bool, ‖s + bsign b • Φ a‖ ^ 2 ≤ ‖s‖ ^ 2 + ‖Φ a‖ ^ 2 →
        ∃ σ' : X → Bool, ‖∑ x ∈ insert a S, bsign (σ' x) • Φ x‖ ^ 2 ≤
          ∑ x ∈ insert a S, ‖Φ x‖ ^ 2 := by
      intro b hb
      refine ⟨Function.update σ a b, ?_⟩
      have hS : ∑ x ∈ S, bsign (Function.update σ a b x) • Φ x = s := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Function.update_of_ne (by rintro rfl; exact ha hx)]
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Function.update_self, hS, add_comm]
      linarith
    by_cases h : ‖s + Φ a‖ ^ 2 ≤ ‖s‖ ^ 2 + ‖Φ a‖ ^ 2
    · exact key true (by simpa [bsign] using h)
    · refine key false ?_
      have : ‖s - Φ a‖ ^ 2 ≤ ‖s‖ ^ 2 + ‖Φ a‖ ^ 2 := by linarith
      simpa [bsign, sub_eq_add_neg] using this

/-- Convex separation and ordinary dimension (`lem:geometry`), margin and VC parts: if every
marginal on a nonempty finite domain gives kernel correlation at least `c`, each target has a
unit separator with margin `c` on every point, and every shattered set has at most `1/(2c²)`
points. -/
theorem margin_and_vc {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] (Φ : X → K)
    (hΦ : ∀ x, ‖Φ x‖ ^ 2 ≤ 1 / 2)
    (H : Finset (X → Bool)) {c : ℝ} (hc : 0 < c)
    (hall : ∀ h ∈ H, ∀ p : X → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      c ≤ ‖∑ x, (p x * bsign (h x)) • Φ x‖) :
    (∀ h ∈ H, ∃ u : K, ‖u‖ = 1 ∧ ∀ x, c ≤ bsign (h x) * ⟪u, Φ x⟫) ∧
    (∀ S : Finset X, Shatters H S → (S.card : ℝ) ≤ 1 / (2 * c ^ 2)) := by
  have margin : ∀ h ∈ H, ∃ u : K, ‖u‖ = 1 ∧ ∀ x, c ≤ bsign (h x) * ⟪u, Φ x⟫ := by
    intro h hh
    let L : (X → ℝ) →ₗ[ℝ] K := Fintype.linearCombination ℝ (fun x => bsign (h x) • Φ x)
    let Q : Set (X → ℝ) := {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}
    have hQc : IsCompact Q := by
      refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
        ?_ ?_
      · have h1 : IsClosed {p : X → ℝ | ∀ x, 0 ≤ p x} := by
          simp only [Set.ofPred_forall]
          exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
        have h2 : IsClosed {p : X → ℝ | ∑ x, p x = 1} :=
          isClosed_eq (continuous_finsetSum _ fun x _ => continuous_apply x) continuous_const
        exact h1.inter h2
      · rintro p ⟨hp0, hp1⟩ x -
        refine ⟨hp0 x, ?_⟩
        rw [← hp1]
        exact Finset.single_le_sum (fun y _ => hp0 y) (Finset.mem_univ x)
    have hQconv : Convex ℝ Q := by
      rintro p ⟨hp0, hp1⟩ q ⟨hq0, hq1⟩ a b ha hb hab
      refine ⟨fun x => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hp0 x; have := hq0 x; positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hp1, hq1]
        linarith
    have hsingle : ∀ x, Pi.single x (1 : ℝ) ∈ Q := by
      intro x
      refine ⟨fun y => ?_, by simp⟩
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy]
    have hLsingle : ∀ x, L (Pi.single x 1) = bsign (h x) • Φ x := by
      intro x; simp [L]
    have hKc : IsCompact (L '' Q) := hQc.image L.continuous_of_finiteDimensional
    have hKconv : Convex ℝ (L '' Q) := hQconv.linear_image L
    have hKne : (L '' Q).Nonempty := ⟨_, Set.mem_image_of_mem L (hsingle (Classical.arbitrary X))⟩
    obtain ⟨v, hvK, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete hKconv 0
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero hKconv hvK).1 hvmin
    obtain ⟨p, ⟨hp0, hp1⟩, rfl⟩ := hvK
    have hcv : c ≤ ‖L p‖ := by
      have := hall h hh p hp0 hp1
      simpa [L, Fintype.linearCombination_apply, smul_smul] using this
    have hpos : 0 < ‖L p‖ := hc.trans_le hcv
    refine ⟨‖L p‖⁻¹ • L p, by simp [norm_smul, hpos.ne'], fun x => ?_⟩
    have hx := hvar _ (Set.mem_image_of_mem L (hsingle x))
    rw [hLsingle] at hx
    have hx' : ‖L p‖ ^ 2 ≤ bsign (h x) * ⟪L p, Φ x⟫ := by
      rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq] at hx
      linarith
    rw [real_inner_smul_left, ← mul_assoc, mul_comm (bsign (h x)), mul_assoc, le_inv_mul_iff₀ hpos]
    nlinarith
  refine ⟨margin, fun S hS => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_signs_norm_sq_le Φ S
  obtain ⟨h, hh, hhσ⟩ := hS σ
  obtain ⟨u, hu1, hu⟩ := margin h hh
  set s := ∑ x ∈ S, bsign (σ x) • Φ x
  have h1 : (S.card : ℝ) * c ≤ ⟪u, s⟫ := by
    rw [inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [real_inner_smul_right, ← hhσ x hx]
    exact hu x
  have h2 : ⟪u, s⟫ ≤ ‖s‖ := by
    simpa [hu1] using real_inner_le_norm u s
  have h3 : ‖s‖ ^ 2 ≤ S.card / 2 := by
    refine hσ.trans ?_
    calc ∑ x ∈ S, ‖Φ x‖ ^ 2 ≤ ∑ x ∈ S, (1 / 2 : ℝ) := Finset.sum_le_sum fun x _ => hΦ x
      _ = S.card / 2 := by simp [div_eq_mul_inv]
  have h4 : ((S.card : ℝ) * c) ^ 2 ≤ S.card / 2 := by
    have h0 : 0 ≤ (S.card : ℝ) * c := by positivity
    nlinarith
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · rw [h0]; simp; positivity
  · have hS0 : (0 : ℝ) < S.card := by exact_mod_cast h0
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- Convex separation and ordinary dimension (`lem:geometry`), growth part: a class all of whose shattered sets have at most `v`
points has at most `∑_{i ≤ v} (M choose i)` members, `M = |X|`. -/
theorem growth_bound {X : Type*} [Fintype X] [DecidableEq X] (H : Finset (X → Bool)) (v : ℕ)
    (hv : ∀ S : Finset X, Shatters H S → S.card ≤ v) :
    H.card ≤ ∑ i ∈ Finset.range (v + 1), (Fintype.card X).choose i := by
  set tr : (X → Bool) → Finset X := fun h => univ.filter (fun x => h x = true) with htr
  have htr_inj : Function.Injective tr := by
    intro h₁ h₂ he
    funext x
    have := congrArg (fun s => x ∈ s) he
    simp only [htr, mem_filter, mem_univ, true_and, eq_iff_iff] at this
    cases h1 : h₁ x <;> cases h2 : h₂ x <;> simp_all
  set 𝒜 := H.image tr
  have hcard : H.card = 𝒜.card := (card_image_of_injective H htr_inj).symm
  have hsh : ∀ S, 𝒜.Shatters S → Shatters H S := by
    intro S hS σ
    obtain ⟨u, hu, hSu⟩ := hS (filter_subset (fun x => σ x = true) S)
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hu
    refine ⟨h, hh, fun x hx => ?_⟩
    have := congrArg (fun s => x ∈ s) hSu
    simp only [htr, mem_inter, mem_filter, mem_univ, true_and, eq_iff_iff, hx] at this
    cases h1 : h x <;> cases h2 : σ x <;> simp_all
  have hvc : 𝒜.vcDim ≤ v := by
    unfold vcDim
    refine Finset.sup_le fun S hS => hv S (hsh S (mem_shatterer.1 hS))
  rw [hcard]
  refine (card_le_card_shatterer 𝒜).trans (card_shatterer_le_sum_vcDim.trans ?_)
  refine Finset.sum_le_sum_of_subset fun k hk => ?_
  rw [mem_Iic] at hk
  rw [mem_range]
  omega

end GaussianSGD
