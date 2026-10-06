# Lean formalization

Lean 4 (`leanprover/lean4:v4.34.0-rc2`) with Mathlib at revision `2631d1cc`. Paper results are cited
by title and TeX label, so the Lean files do not depend on the numbering of the manuscript.

## Building

```sh
lake exe cache get
python3 verify.py
```

`verify.py` scans the sources for `sorry`, `admit`, `axiom`, `native_decide`, and similar tokens,
runs `lake build` with warnings treated as errors, runs `AxiomAudit.lean`, and checks that every
listed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. It writes
`lean-verification.json`.

## Definitions

`GaussianSGD/Defs.lean` defines the process of the paper (`eq:init`–`eq:tail`): the cube `{-1,1}^n` (as
`Fin n → Bool`), the bias-free network, the simultaneous single-example update with derivative zero
at a zero preactivation, the normalized tail score and its sign with `sgn 0 = 1`, the laws
`N(0, I_n/n)` of the hidden rows and `N(0, I_m/m)` of the output layer, and the risk. A marginal is a
probability vector on the cube, so expectations over samples are finite sums. The risk is the
Lebesgue integral (`lintegral`) over the initialization of the error averaged over histories drawn
from `D^T`. For an integrand not known to be measurable this is the lower integral, so a lower
bound on it is at least as strong as for a measurable integrand, and a premise stated with it is
no stronger. The same file defines the comparison objects of the proofs (`psi`, `Good`, `frozen`,
`mu`, `Rmap`, `Pmap`, `Zsym`) and the kernel correlation `kernelCorr`.

## Map from the paper

| Paper (TeX label) | Lean theorems | File |
|---|---|---|
| Initialization bounds (`lem:init`) | `init_hidden`, `init_output` | `Init.lean` |
| Score comparison through gate changes (`lem:score`) | `score_comparison`, `tail_score_comparison` | `Comparison.lean` |
| Sampling and label effects (`lem:population`) | `frozen_sq_error`, `label_effect`, `tail_sq_error`, `tail_label_effect` | `Population.lean` |
| Density at the beginning of the tail (`lem:density`) | `density_bound` | `Density.lean` |
| Anti-concentration of the symmetric tail (`lem:smallball`) | `smallball`, `null_risk` | `SmallBall.lean` |
| Kernel identity (`eq:kernelidentity`) | `kernel_identity`, `kernelCorr_eq_norm`, `Phi_norm_sq` | `Kernel.lean` |
| Risk controlled by kernel correlation (`thm:risk`) | `risk_lower_bound` | `Risk.lean` |
| A numerical instance (`cor:instance`) | `lossTerm_regime`, `risk_lower_bound_regime` | `Main.lean` |
| Convex separation and ordinary dimension (`lem:geometry`) | `margin_and_vc`, `growth_bound` | `Geometry.lean` |
| Kernel margin from success under every marginal (`thm:margin`) | `kernel_margin`, `lossTerm_le_half`, `regime_of_large`, `kernel_margin_regime` | `Main.lean` |
| Adjacent points (`cor:edge`) | `edge_lower_bound`, `class_constant` | `Edge.lean` |
| Parity obstruction (`cor:parity`) | `parity_lower_bound`, `kernelCorr_parity_sq_le` | `Main.lean`, `Kernel.lean` |
| Row movement (`lem:rows`) | `row_movement` | `GateRegime.lean` |
| Fixed gates at small total step (`thm:gate`) | `gates_fixed`, `exact_representation`, `gateSet_mass`, `gateBound_le`, `measurable_gate_inf`, `gate_pdc`, `gate_small_step` | `GateRegime.lean`, `GateMass.lean` |

`Basic.lean` collects small lemmas used in several files.

## Not formalized

- The dimension bound of `lem:geometry` and `thm:margin`. The Gaussian projection step and its
  chi-square tail bound are not formalized; the formal statements stop at the margin, the VC
  bound, and the Sauer–Shelah count.
- The crossing proposition (`prop:crossings`).

## Proof routes that differ from the text

- Nonexpansivity of the logistic maps and the Jacobian estimates in `lem:smallball` are proved with
  secant slopes of `tanh` and of the logistic function, obtained from the one-variable mean value
  theorem, without Jacobians of the vector-valued maps.
- `score_comparison` bounds the movement of both layers by induction on `t`, in place of the
  bootstrap over the maxima used in the paper; `row_movement` uses the addition formulas for
  `cosh` and `sinh` in place of the expansion of the matrix power.
- `init_hidden` evaluates the two Chernoff exponents at `±1/512` directly, using the exact moment
  generating function of `ReLU(Z)^2`, instead of bounding the second derivative of its logarithm.
- The VC bound in `margin_and_vc` chooses signs one at a time with the parallelogram law.
- Mathlib has no density for the standard Gaussian measure on `ℝ^m`; `DensityGaussian.lean`
  identifies it through characteristic functions before the change of variables in `density_bound`.
