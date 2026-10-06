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

theorem memLp_relu_inner {n : ℕ} (x : Cube n) :
    MemLp (fun w : Vec n => relu ⟪w, pt x⟫) 2 (rowLaw n) := by
  sorry

/-- The feature `Φ(x) ∈ L²(N(0, I_n/n))`. -/
def Phi {n : ℕ} (x : Cube n) : Lp ℝ 2 (rowLaw n) := (memLp_relu_inner x).toLp _

/-- `‖Φ(x)‖² = 1/2` at every cube point. -/
theorem Phi_norm_sq {n : ℕ} (hn : 1 ≤ n) (x : Cube n) : ‖Phi x‖ ^ 2 = 1 / 2 := by
  sorry

/-- `A_D(h) = ‖E_D h(x) Φ(x)‖`. -/
theorem kernelCorr_eq_norm {n : ℕ} (h : Cube n → Bool) (D : Dist n) :
    kernelCorr h D = ‖∑ x, (D.p x * bsign (h x)) • Phi x‖ := by
  sorry

/-- The initialization identity `E_{W₀} ‖μ‖² = A_D(h)²`. -/
theorem kernel_identity {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h : Cube n → Bool) (D : Dist n) :
    ∫ W, ‖mu (psi W) h D‖ ^ 2 ∂(hiddenLaw n m) = kernelCorr h D ^ 2 := by
  sorry

theorem integrable_norm_mu {n m : ℕ} (h : Cube n → Bool) (D : Dist n) :
    Integrable (fun W => ‖mu (psi W) h D‖) (hiddenLaw n m) := by
  sorry

/-- Parity bound from the proof of `cor:parity`: under the uniform marginal,
`A(χ_A)² = λ_k ≤ 1 / (2 (n choose k))` with `k = |A|`. -/
theorem kernelCorr_parity_sq_le {n : ℕ} (hn : 1 ≤ n) (A : Finset (Fin n)) :
    kernelCorr (parity A) (unif n) ^ 2 ≤ 1 / (2 * (n.choose A.card)) := by
  sorry

end GaussianSGD
