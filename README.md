# Ordinary Dimension from Finite-Time Gaussian Logistic SGD

This package contains a research manuscript, its LaTeX source, and executable
checks for the formulas used in the proofs.

The main theorem is for the exact two-layer, bias-free Gaussian-initialized
logistic-SGD process, with simultaneous single-example updates and tail-sum
prediction. Set B = eta * m * T. If m >= 2^20 n, T >= 2^24, and 0 < B <= 12,
then success to expected error epsilon < 1/4 for every target and every input
marginal implies ordinary dimension at most C(n+1), for a universal constant C.
The proof derives a Gaussian ReLU kernel margin of at least 1/(72B).

The paper also proves a quantitative risk lower bound and a high-order parity
obstruction. A separate proposition shows that arbitrarily many gates can
cross in the first exact update in a linear-width scaling within this regime.
No convergence experiment or unconditional feature-learning separation is claimed.

## Files

- ordinary_dimension.pdf: the manuscript.
- ordinary_dimension.tex: complete source, including its TikZ figure and bibliography.
- AUDIT.md: assumptions, proof dependencies, and scope of the checks.
- verify.py: exact rational constant checks and finite floating-point diagnostics.
- verification_results.json: saved results from the supplied script.
- build.sh: PDF build command.
- SHA256SUMS: hashes of the delivered files other than this manifest.

## Rebuilding

A TeX distribution providing jmlr.cls, TikZ, mathtools, microtype, and Latin Modern
is required. Run `./build.sh`. The source uses the PMLR options of the JMLR class.
The distribution's class and fonts are dependencies, not bundled assets.

The checks need Python 3.10 or later and NumPy. Run:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python verify.py

The rational constant calculations are exact. The trajectory and Jacobian
calculations use floating point. They are diagnostics of the proof formulas,
not formal proof verification or a finite-bit simulation theorem for exact SGD.
