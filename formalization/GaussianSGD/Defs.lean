import Mathlib

/-!
# Definitions

The Boolean cube, the bias-free two-layer ReLU network, the exact simultaneous
single-example logistic SGD update, the tail-averaged classifier, the Gaussian
initialization, the risk, and the comparison recurrences used in the proofs.

Notation follows the paper: `n` is the input dimension, `m` the width, `T` the
number of updates, `η` the step size, `γ = η m`, and `B = η m T`.
-/

noncomputable section

open scoped RealInnerProductSpace
open Finset MeasureTheory ProbabilityTheory

namespace GaussianSGD

/-- Euclidean space `ℝ^k`. -/
abbrev Vec (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The cube `{-1,1}^n`, with points encoded by sign bits. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `true ↦ 1` and `false ↦ -1`. -/
def bsign (b : Bool) : ℝ := if b then 1 else -1

/-- A cube point as a vector with entries `±1`. -/
def pt {n : ℕ} (x : Cube n) : Vec n := WithLp.toLp 2 (fun i => bsign (x i))

/-- The rectified linear unit. -/
def relu (z : ℝ) : ℝ := max z 0

/-- The sign function with `sgn 0 = 1`. -/
def sgn (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

/-- The logistic multiplier `g(y,z) = y / (1 + exp(y z))`. The SGD coefficient
on a labeled example `(x,y)` is `η g(y, f(x))`. -/
def g (y z : ℝ) : ℝ := y / (1 + Real.exp (y * z))

/-- Network parameters: hidden rows `W j ∈ ℝ^n` and output weights `a ∈ ℝ^m`. -/
abbrev Params (n m : ℕ) := (Fin m → Vec n) × Vec m

/-- Hidden activations `ReLU(W x)`. -/
def hid {n m : ℕ} (W : Fin m → Vec n) (x : Cube n) : Vec m :=
  WithLp.toLp 2 (fun j => relu ⟪W j, pt x⟫)

/-- The score `f(x) = aᵀ ReLU(W x)`. -/
def score {n m : ℕ} (θ : Params n m) (x : Cube n) : ℝ := ⟪θ.2, hid θ.1 x⟫

/-- One exact simultaneous update with step `η` on the labeled example `(x,y)`.
Both layers use the old parameters, and a zero preactivation has derivative zero. -/
def step {n m : ℕ} (η : ℝ) (θ : Params n m) (x : Cube n) (y : ℝ) : Params n m :=
  (fun j => θ.1 j + (η * g y (score θ x) * θ.2 j * (if 0 < ⟪θ.1 j, pt x⟫ then 1 else 0)) • pt x,
   θ.2 + (η * g y (score θ x)) • hid θ.1 x)

/-- Parameters after `t` updates on the labeled sequence `(xs t, ys t)`. -/
def traj {n m : ℕ} (η : ℝ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ) :
    ℕ → Params n m
  | 0 => θ0
  | t + 1 => step η (traj η θ0 xs ys t) (xs t) (ys t)

/-- The tail indices `{⌈T/2⌉, …, T}`. -/
def tail (T : ℕ) : Finset ℕ := Finset.Icc ((T + 1) / 2) T

/-- Average over the tail indices. -/
def tailAvg {k : ℕ} (T : ℕ) (u : ℕ → Vec k) : Vec k :=
  ((tail T).card : ℝ)⁻¹ • ∑ t ∈ tail T, u t

/-- The normalized tail score `F(x) = q⁻¹ ∑_{t ∈ I_T} f_t(x)`. -/
def tailScore {n m : ℕ} (η : ℝ) (T : ℕ) (θ0 : Params n m) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (x : Cube n) : ℝ :=
  ((tail T).card : ℝ)⁻¹ * ∑ t ∈ tail T, score (traj η θ0 xs ys t) x

/-- A probability distribution on the cube. -/
structure Dist (n : ℕ) where
  p : Cube n → ℝ
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x, p x = 1

/-- Extends a length-`T` history to a sequence. Entries after `T` are never used. -/
def ext {n T : ℕ} (s : Fin T → Cube n) : ℕ → Cube n :=
  fun t => if ht : t < T then s ⟨t, ht⟩ else fun _ => true

/-- Labels `y_t = h(x_t)` of a sample sequence. -/
def labels {n : ℕ} (h : Cube n → Bool) (xs : ℕ → Cube n) : ℕ → ℝ := fun t => bsign (h (xs t))

/-- Probability of a history under `D^T`. -/
def histWeight {n T : ℕ} (D : Dist n) (s : Fin T → Cube n) : ℝ := ∏ i, D.p (s i)

/-- Classification error `Pr_{x∼D}[G(x) ≠ h(x)]` of a `±1`-valued predictor `G`. -/
def err {n : ℕ} (D : Dist n) (G : Cube n → ℝ) (h : Cube n → Bool) : ℝ :=
  ∑ x, D.p x * (if G x = bsign (h x) then 0 else 1)

/-- Expected error of the returned classifier `sign F` given the initialization,
averaged over training histories drawn from `D^T`. -/
def condErr {n m : ℕ} (η : ℝ) (T : ℕ) (θ0 : Params n m) (h : Cube n → Bool) (D : Dist n) : ℝ :=
  ∑ s : Fin T → Cube n,
    histWeight D s * err D (fun x => sgn (tailScore η T θ0 (ext s) (labels h (ext s)) x)) h

/-- Law of one hidden row, `N(0, I_n / n)`. -/
def rowLaw (n : ℕ) : Measure (Vec n) :=
  (stdGaussian (Vec n)).map (fun v => (Real.sqrt n)⁻¹ • v)

/-- Law of the hidden layer: independent rows with law `rowLaw n`. -/
def hiddenLaw (n m : ℕ) : Measure (Fin m → Vec n) := Measure.pi (fun _ => rowLaw n)

/-- Law of the output weights, `N(0, I_m / m)`. -/
def outLaw (m : ℕ) : Measure (Vec m) :=
  (stdGaussian (Vec m)).map (fun v => (Real.sqrt m)⁻¹ • v)

/-- The risk `E_{W₀,a₀,(x_t)} Pr_{x∼D}[G(x) ≠ h(x)]` of the exact process. -/
def risk {n : ℕ} (m : ℕ) (η : ℝ) (T : ℕ) (h : Cube n → Bool) (D : Dist n) : ENNReal :=
  ∫⁻ W, ∫⁻ a, ENNReal.ofReal (condErr η T (W, a) h D) ∂(outLaw m) ∂(hiddenLaw n m)

/-! ### Comparison objects -/

/-- Normalized initial features `ψ(x) = m^{-1/2} ReLU(W₀ x)`. -/
def psi {n m : ℕ} (W : Fin m → Vec n) (x : Cube n) : Vec m := (Real.sqrt m)⁻¹ • hid W x

/-- The good event `𝒢`: `7/16 ≤ ‖ψ(x)‖² ≤ 9/16` at every cube point. -/
def Good {n m : ℕ} (W : Fin m → Vec n) : Prop :=
  ∀ x : Cube n, 7 / 16 ≤ ‖psi W x‖ ^ 2 ∧ ‖psi W x‖ ^ 2 ≤ 9 / 16

/-- The linear (frozen-feature) logistic SGD recurrence on the same labeled samples:
`u₀ = b₀` and `u_{t+1} = u_t + γ g(y_t, ⟪u_t, ψ(x_t)⟫) ψ(x_t)`. -/
def frozen {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (xs : ℕ → Cube n) (ys : ℕ → ℝ)
    (b0 : Vec m) : ℕ → Vec m
  | 0 => b0
  | t + 1 =>
      frozen γ ψ xs ys b0 t + (γ * g (ys t) ⟪frozen γ ψ xs ys b0 t, ψ (xs t)⟫) • ψ (xs t)

/-- Label correlation of the features, `μ = E_D h(x) ψ(x)`. -/
def mu {n m : ℕ} (ψ : Cube n → Vec m) (h : Cube n → Bool) (D : Dist n) : Vec m :=
  ∑ x, (D.p x * bsign (h x)) • ψ x

/-- The label-symmetric population map
`R(v) = v - (γ/2) E_D[ψ(x) tanh(⟪v, ψ(x)⟫/2)]`. -/
def Rmap {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (v : Vec m) : Vec m :=
  v - (γ / 2) • ∑ x, (D.p x * Real.tanh (⟪v, ψ x⟫ / 2)) • ψ x

/-- The population map `P = R + γ μ / 2`. -/
def Pmap {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (h : Cube n → Bool) (D : Dist n)
    (v : Vec m) : Vec m :=
  Rmap γ ψ D v + (γ / 2) • mu ψ h D

/-- The symmetric tail score `Z_D(x; b₀) = ⟪z̄(b₀), ψ(x)⟫` with `z_t = R^t(b₀)`. -/
def Zsym {n m : ℕ} (γ : ℝ) (ψ : Cube n → Vec m) (D : Dist n) (T : ℕ) (x : Cube n)
    (b0 : Vec m) : ℝ :=
  ⟪tailAvg T (fun t => (Rmap γ ψ D)^[t] b0), ψ x⟫

/-! ### Kernel -/

/-- Gaussian ReLU kernel correlation `A_D(h) = ‖E_D h(x) Φ(x)‖` in
`L²(N(0, I_n/n))`, written through its square
`A_D(h)² = E_w (E_D h(x) ReLU⟪w, x⟫)²`. -/
def kernelCorr {n : ℕ} (h : Cube n → Bool) (D : Dist n) : ℝ :=
  Real.sqrt (∫ w, (∑ x, D.p x * bsign (h x) * relu ⟪w, pt x⟫) ^ 2 ∂(rowLaw n))

/-- The parity `χ_A(x) = ∏_{i ∈ A} x_i`, as a Boolean target. -/
def parity {n : ℕ} (A : Finset (Fin n)) : Cube n → Bool :=
  fun x => decide (∏ i ∈ A, bsign (x i) = 1)

/-- The uniform distribution on the cube. -/
def unif (n : ℕ) : Dist n where
  p := fun _ => 1 / 2 ^ n
  nonneg := fun _ => by positivity
  sum_one := by simp

/-! ### Constants of `thm:risk` -/

/-- `ρ_W = min {1, 2^{n+1} e^{-m/16384}}`. -/
def rhoW (n m : ℕ) : ℝ := min 1 (2 ^ (n + 1) * Real.exp (-(m : ℝ) / 16384))

/-- `ρ_a = e^{-m/2}`. -/
def rhoA (m : ℕ) : ℝ := Real.exp (-(m : ℝ) / 2)

/-- `κ = 544 n / m`. -/
def kappa (n m : ℕ) : ℝ := 544 * n / m

/-- The loss `Δ = ρ_W/2 + ρ_a + 24κ + 27B/√T` in `thm:risk`. -/
def lossTerm (n m T : ℕ) (B : ℝ) : ℝ :=
  rhoW n m / 2 + rhoA m + 24 * kappa n m + 27 * B / Real.sqrt T

/-- A finite set of points is shattered by a class of Boolean functions. -/
def Shatters {X : Type*} (H : Finset (X → Bool)) (S : Finset X) : Prop :=
  ∀ σ : X → Bool, ∃ h ∈ H, ∀ x ∈ S, h x = σ x

end GaussianSGD
