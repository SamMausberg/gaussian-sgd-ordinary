import GaussianSGD.Defs

/-!
# Convex separation and the VC bound (`lem:geometry`)
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace GaussianSGD

/-- Convex separation and ordinary dimension (`lem:geometry`), margin and VC parts: if every marginal gives kernel correlation at
least `c`, each target has a unit separator with margin `c` on every point, and
every shattered set has at most `1/(2c²)` points. -/
theorem margin_and_vc {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {X : Type*} [Fintype X] [DecidableEq X] (Φ : X → K) (hΦ : ∀ x, ‖Φ x‖ ^ 2 ≤ 1 / 2)
    (H : Finset (X → Bool)) {c : ℝ} (hc : 0 < c)
    (hall : ∀ h ∈ H, ∀ p : X → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      c ≤ ‖∑ x, (p x * bsign (h x)) • Φ x‖) :
    (∀ h ∈ H, ∃ u : K, ‖u‖ = 1 ∧ ∀ x, c ≤ bsign (h x) * ⟪u, Φ x⟫) ∧
    (∀ S : Finset X, Shatters H S → (S.card : ℝ) ≤ 1 / (2 * c ^ 2)) := by
  sorry

/-- Convex separation and ordinary dimension (`lem:geometry`), growth part: a class all of whose shattered sets have at most `v`
points has at most `∑_{i ≤ v} (M choose i)` members, `M = |X|`. -/
theorem growth_bound {X : Type*} [Fintype X] [DecidableEq X] (H : Finset (X → Bool)) (v : ℕ)
    (hv : ∀ S : Finset X, Shatters H S → S.card ≤ v) :
    H.card ≤ ∑ i ∈ Finset.range (v + 1), (Fintype.card X).choose i := by
  sorry

end GaussianSGD
