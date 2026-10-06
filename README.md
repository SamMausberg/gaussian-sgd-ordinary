# Bounded-time logistic SGD requires Gaussian ReLU kernel correlation

Manuscript, Lean formalization, and numerical checks for the paper of the same name.

The paper studies the two-layer bias-free ReLU network of Feldman, Kamath, and Srebro's
Open Question 1, trained on `{-1,1}^n` by exact single-example logistic SGD with Gaussian
initialization and the tail-sum predictor. At bounded effective time `B = ηmT ≤ 12` it shows that
the risk on a target `h` under a marginal `D` is at least `1/2 - Δ - 9B A_D(h)`, where `A_D(h)` is
the label correlation of the Gaussian ReLU features. Success under every marginal then gives every
target a margin in that kernel, bounded VC dimension, and dimension complexity `O(n)`.

## Layout

- `paper/main.tex`: the manuscript (PMLR layout of the `jmlr` class). `paper/build.sh` builds
  `main.pdf`.
- `formalization/`: Lean 4 and Mathlib development. See `formalization/README.md` for the map
  from paper statements to Lean theorems and for what is not formalized.
- `checks/verify.py`: exact rational checks of the constants and floating-point checks of proof
  formulas on small instances; `checks/verification_results.json` holds its output.
- `history/`: the manuscript and the fixed-gate note as first received.

## Building

The paper needs a TeX distribution with `jmlr.cls` (TeX Live package `texlive-publishers`), TikZ,
`mathtools`, `microtype`, `booktabs`, and Latin Modern. Run `paper/build.sh`.

The Lean development pins its toolchain and Mathlib revision. With `elan` installed:

```sh
cd formalization
lake exe cache get
python3 verify.py
```

The checks need Python 3.10 or later and NumPy:

```sh
OPENBLAS_NUM_THREADS=1 python3 checks/verify.py
```
