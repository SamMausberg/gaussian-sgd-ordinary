# Proof and source audit

## Claim being proved

The principal conclusion is ordinary, deterministic, exact dimension complexity.
The learning premise is quantified as follows. The dimension n, width m, number
of updates T, and positive step size eta are selected before the pair (h,D).
For every target h in H and every probability distribution D on the full
Boolean cube, the expected classification error of the prescribed learner,
averaging its Gaussian initialization and its independent training examples,
is at most one common epsilon < 1/4.

The sufficient regime is m >= 2^20 n, T >= 2^24, and 0 < B = eta*m*T <= 12.
The quantitative risk theorem only requires m >= 576 n, B <= 12, and
eta*m <= 1/2. Its error losses remain explicit.

## Exact process

Both update equations use the parameters at time t. An input-layer gate at zero
has derivative zero. The tail uses all indices from ceil(T/2) through T,
including T. Dividing by its positive length does not change its sign. Scores
are thresholded with sign(0)=+1.

The frozen-feature, population, and label-symmetric recurrences occur solely in
the proof. None replaces a step of the trained network. The proof does not use
finite-precision gradients, batches, added noise, or a different initialization.

## Deterministic comparison

The hidden-layer good event bounds squared normalized feature norms between
7/16 and 9/16 at every cube point. Its probability is controlled by a union
bound over cube points, not over training histories. It is independent of the
target and marginal.

The actual/frozen score comparison is uniform over every labeled history and
every test point on this event and the event ||a_0|| <= 2. A bound on actual
Frobenius displacement, together with the global Lipschitz property of ReLU,
controls changes across gate boundaries. Every occurrence of a trained
output coefficient uses the original simultaneous update. No gate-stability
assumption enters this comparison.

The unrounded upper bound on the coefficient of n/m is 516+18=534. The
manuscript uses the looser value 544 throughout.

## Population coupling and dependence

Conditional on each W_0 and b_0=sqrt(m)*a_0, the frozen stochastic recurrence has
its stated population recurrence as its conditional mean. Fresh samples make
its centered noise a martingale difference. The sample maps and population map
are nonexpansive, giving conditional mean-square error at most
T*gamma^2*(9/16).

The classification conversion uses this conditional second-moment bound. It
integrates the conditional Markov bound against the symmetric score's
small-ball distribution. No independence of the stochastic error and the
symmetric score is asserted. This yields a loss 27B/sqrt(T). Conditioning the
Gaussian output initialization on a norm ball would invalidate the stated
Gaussian calculation; instead the proof subtracts that ball's failure
probability after applying the unrestricted Gaussian estimate.

## Density and anti-concentration

For the label-symmetric population map R, the Hessian term is positive
semidefinite, has operator norm at most 9/64, and has trace at most 9/64.
The trace bound makes the determinant estimate independent of m.

R is the gradient of a strongly convex potential when gamma <= 1/2.
Subtracting a linear functional gives a coercive strongly convex function,
which proves surjectivity. Strong monotonicity proves injectivity. Thus change
of variables applies to the global smooth inverse.

At the beginning of the tail, the log density ratio to a standard Gaussian is
at most 225/238. Norm contraction and the determinant chain rule provide this
bound. The remaining tail has effective duration at most B/2. Its Jacobian
products need not commute or be symmetric. The proof only uses their
operator-norm distance from identity, giving a directional derivative at least
5*sqrt(7)/128. Artificially assigning a standard Gaussian to the tail-start
state yields small-ball coefficient less than 8; density domination then gives
coefficient less than 24 for its actual law.

The symmetric tail is odd in the initial output coefficients. Anti-concentration
excludes atoms at zero, so its expected classification error is exactly 1/2 for
every fixed target and marginal.

## Constants and kernel margin

At the main theorem's parameter thresholds, the subtracted losses are bounded
by (32+64+324+51)/4096 = 471/4096 < 1/8. Therefore

    risk(h,D) >= 3/8 - 9 B || E_D h(x) Phi(x) ||.

The kernel feature Phi(x)(w)=ReLU(w.x), w~N(0,I/n), is fixed before h,D and
satisfies ||Phi(x)||^2=1/2. The initialization identity for squared empirical
label correlation is used before restricting to the good hidden-layer event.
Cauchy-Schwarz then bounds the good-event average without changing the kernel.

All-distribution success implies that every point of the convex hull of the
signed kernel features has norm at least 1/(72B). Its nearest point gives one
unit separator with that margin for all cube points. This separator depends on
the target, not the marginal. The main feature map remains common.

The VC and Gaussian-projection arguments are standard finite-set geometry;
full proofs are included. The Gaussian projection is selected once for the
entire finite target class. The resulting ordinary representation is strict
and deterministic. Its existence does not assert efficient construction.

## Crossing and parity propositions

The first-step crossing calculation uses the old Gaussian output weights. A
binomial set of candidate rows crosses whenever the initial score is bounded
above. Its size and the initial score are dependent; the proof uses a union
bound, not independence. Taking the dimension limit before the score cutoff
limit proves the stated convergence in probability. This proposition needs no
learning assumption and makes no assertion about a positive limiting fraction
of changed gates.

For parities, permutation invariance makes expected squared Fourier
coefficients equal within each degree. Parseval bounds their sum by 1/2.
Substituting into the risk theorem gives the stated finite-parameter
obstruction. The obstruction is specific to the theorem's regime.

## Executable checks

The supplied script passed 11 exact Fraction assertions for the constant
calculations. Numerical grids check the centered Gaussian moment-generating
function inequality and the logistic decomposition. Eighteen finite trajectory
cases check the actual simultaneous updates against frozen and population
recurrences; they include Gaussian hidden weights and balanced deterministic
hidden weights with zero preactivations. The deterministic cases test lemmas
that apply to any hidden layer in the stated good event. They do not replace
the initialization of the learning theorem.

A further 108 cases check density-ratio and Jacobian formulas under uniform,
point-mass, and irregular finite marginals. The largest observed chain-rule
log-determinant residual is about 4.9e-15. The smallest tested directional
derivative was about 0.495, above the proved lower bound about 0.103. These
finite checks use smaller T than the conservative main theorem threshold;
they test the auxiliary lemmas, not a distribution-free learning guarantee.

The proofs are analytic. These computations are neither formal verification
nor evidence that the process converges on an unexamined concept class.

## Primary sources and attribution

The work was positioned against the following primary sources. The proof does
not import an approximate-gradient result.

Chizat, Oyallon, and Bach, arXiv:1812.07956: scaling and comparison to fixed-kernel
behavior. Allen-Zhu, Li, and Liang, arXiv:1811.04918v6, Section 6.2: frozen-gate
pseudo networks retaining products of trained matrices. Ji and Telgarsky,
arXiv:1909.12292v4: logistic gradient methods with fixed output signs and a
separability assumption in tangent features. Daniely, arXiv:1702.08503:
comparator-dependent conjugate-kernel learning guarantees.

The COLT papers used for related-work checking and structure were Malach et al.,
PMLR 134:3265-3295 (especially Remarks 8 and 10); Yehudai and Shamir,
PMLR 125:3756-3786; and Kamath, Montasser, and Srebro, PMLR 125:2236-2262.
KMS Section 2.3 records the classical margin-to-ordinary-dimension conversion.
That conversion is not claimed as new.

The FKS official landing page and bibliographic metadata were checked. The
process is defined fully in the manuscript from the formulation supplied in
this research thread; no claim is made that an unavailable full-text retrieval
was read.

## Scope

This is a bounded-effective-time kernel-regime theorem. The numerical constants
are conservative sufficient conditions, not a sharp transition. Many gate
crossings are compatible with the score comparison, but they do not establish
a feature-learning separation. The result neither settles unrestricted
ordinary dimension for this SGD process nor gives a theorem for B growing
with input dimension. No computational hardness assumption is used.
