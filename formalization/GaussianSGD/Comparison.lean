import GaussianSGD.Defs

/-!
# Score comparison through gate changes (`lem:score`)

On the good event for the hidden layer and with `‖a₀‖ ≤ 2`, the exact network's
score stays within `κ = 544 n / m` of the frozen-feature linear recurrence, for every
labeled history and every cube point. No gate-stability assumption is used.
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset

namespace GaussianSGD

/-- Score comparison through gate changes (`lem:score`). -/
theorem score_comparison {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 < η)
    (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2)
    (θ0 : Params n m) (hG : Good θ0.1) (ha : ‖θ0.2‖ ≤ 2)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, ys t = 1 ∨ ys t = -1)
    (t : ℕ) (ht : t ≤ T) (x : Cube n) :
    |score (traj η θ0 xs ys t) x -
        ⟪frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2) t, psi θ0.1 x⟫| ≤ kappa n m := by
  sorry

/-- Score comparison through gate changes (`lem:score`), tail-averaged form. -/
theorem tail_score_comparison {n m T : ℕ} (hn : 1 ≤ n) (hm : 576 * n ≤ m) {η : ℝ} (hη : 0 < η)
    (hB : η * m * T ≤ 12) (hγ : η * m ≤ 1 / 2)
    (θ0 : Params n m) (hG : Good θ0.1) (ha : ‖θ0.2‖ ≤ 2)
    (xs : ℕ → Cube n) (ys : ℕ → ℝ) (hys : ∀ t, ys t = 1 ∨ ys t = -1) (x : Cube n) :
    |tailScore η T θ0 xs ys x -
        ⟪tailAvg T (frozen (η * m) (psi θ0.1) xs ys (Real.sqrt m • θ0.2)), psi θ0.1 x⟫|
      ≤ kappa n m := by
  sorry

end GaussianSGD
