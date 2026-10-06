#!/usr/bin/env python3
"""Reproducible diagnostics for ordinary_dimension.tex.

The Fraction checks are exact arithmetic. NumPy calculations are finite
floating-point checks of the proof's formulas, not an implementation theorem
for exact real SGD and not evidence of distribution-free convergence.
"""
from __future__ import annotations

import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]
LAMBDA = 9 / 16
LOWER = 7 / 16


def cube(n: int) -> Array:
    return np.array(list(itertools.product((-1.0, 1.0), repeat=n)), dtype=float)


def sigmoid(x: Array | float) -> Array:
    a = np.asarray(x, dtype=float)
    return np.exp(-np.logaddexp(0.0, -a))


def constants() -> dict:
    lam, B = F(9, 16), F(12)
    density = F(25, 4) * lam / (4 * (1 - lam / 8))
    first_score = (1 + B * lam / 4) * 16 * B
    second_score = 4 * B * B * F(3, 4) / 24
    total = F(32 + 64 + 324 + 51, 4096)
    assert density == F(225, 238) < 1
    assert first_score == 516 and second_score == 18
    assert first_score + second_score <= 544
    assert total == F(471, 4096) < F(1, 8)
    assert F(27) * B / 4096 == F(324, 4096)
    assert F(24 * 544, 2**20) == F(51, 4096)
    assert 256**2 < 8**2 * 25 * 14 * 3  # pi > 3 implies the bound < 8.
    assert F(12, 2**24) < F(1, 2)
    assert F(2) + F(3, 8) < 4 * (1 - F(1, 4))
    assert F(72**2, 2) == 2592
    # Chernoff exponents at the stated tilt.
    theta = F(1, 512)
    assert theta / 16 - 16 * theta * theta == F(1, 16384)
    return {
        "exact_fraction_checks": 11,
        "risk_loss_budget": str(total),
        "available_budget": "1/8",
        "density_log_ratio_bound": str(density),
        "score_coefficient_upper_bound": str(first_score + second_score),
        "stated_score_coefficient": 544,
        "gaussian_small_ball_coefficient": 256 / (5 * math.sqrt(14 * math.pi)),
        "dominated_coefficient_upper_bound": 8 * math.e,
    }


def analytic_grids() -> dict:
    theta = np.linspace(-0.25, 0.25, 20001)
    mgf = (1 + (1 - 2 * theta) ** -0.5) / 2
    rhs = 16 * theta**2
    excess = np.log(mgf) - theta / 2 - rhs
    assert float(excess.max()) <= 1e-12
    z = np.linspace(-100, 100, 10001)
    residual = 0.0
    for y in (-1.0, 1.0):
        g = y * sigmoid(-y * z)
        alt = y / 2 - 0.5 * np.tanh(z / 2)
        residual = max(residual, float(np.max(np.abs(g - alt))))
    assert residual < 1e-14
    return {"mgf_grid_points": len(theta), "mgf_max_excess": float(excess.max()),
            "logistic_grid_points": 2 * len(z), "logistic_identity_residual": residual}


def null_map(v: Array, psi: Array, mass: Array, gamma: float) -> Array:
    return v - gamma * ((mass * np.tanh((psi @ v) / 2)) @ psi) / 2


def null_hessian(v: Array, psi: Array, mass: Array) -> Array:
    q = np.tanh((psi @ v) / 2)
    return (psi.T * (mass * (1 - q**2) / 4)) @ psi


def trajectory_checks() -> dict:
    rng = np.random.default_rng(171805)
    cases = []
    for n in (2, 3, 4):
        X = cube(n)
        m = 768 * n
        assert m % len(X) == 0
        for init in ("balanced_cube", "gaussian"):
            W0 = (np.tile(X, (m // len(X), 1)) / math.sqrt(n)
                  if init == "balanced_cube" else rng.normal(size=(m, n)) / math.sqrt(n))
            psi = np.maximum(X @ W0.T, 0) / math.sqrt(m)
            norms = np.sum(psi**2, axis=1)
            assert norms.min() >= LOWER and norms.max() <= LAMBDA
            a0 = rng.normal(size=m) / math.sqrt(m)
            assert np.linalg.norm(a0) <= 2
            mass = rng.dirichlet(np.ones(len(X)))
            labels = np.prod(X[:, :2], axis=1)
            mu = (mass * labels) @ psi
            for B in (0.5, 6.0, 12.0):
                T = 64
                gamma, eta = B / T, B / (m * T)
                W, a = W0.copy(), a0.copy()
                u = math.sqrt(m) * a0
                pop, null = u.copy(), u.copy()
                old_gates = X @ W0.T > 0
                max_score_diff = 0.0
                max_a = np.linalg.norm(a)
                max_displacement = 0.0
                max_changed = 0
                sum_score = np.zeros(len(X))
                sum_frozen = np.zeros(len(X))
                tail_count = 0
                for t in range(T + 1):
                    acts = np.maximum(X @ W.T, 0)
                    score = acts @ a
                    frozen = psi @ u
                    max_score_diff = max(max_score_diff, float(np.max(np.abs(score - frozen))))
                    max_a = max(max_a, float(np.linalg.norm(a)))
                    max_displacement = max(max_displacement, float(np.linalg.norm(W - W0)))
                    max_changed = max(max_changed, int(np.count_nonzero((X @ W.T > 0) != old_gates)))
                    assert np.linalg.norm(pop - null) <= t * gamma * np.linalg.norm(mu) / 2 + 1e-9
                    if t >= (T + 1) // 2:
                        sum_score += score
                        sum_frozen += frozen
                        tail_count += 1
                    if t == T:
                        break
                    j = rng.choice(len(X), p=mass)
                    x, y = X[j], labels[j]
                    pre = W @ x
                    c = eta * y * float(sigmoid(-y * score[j]))
                    # Both updates explicitly use the old coefficients.
                    W_new = W + c * (a * (pre > 0))[:, None] * x[None, :]
                    a_new = a + c * np.maximum(pre, 0)
                    u = u + gamma * y * float(sigmoid(-y * float(psi[j] @ u))) * psi[j]
                    pop = null_map(pop, psi, mass, gamma) + gamma * mu / 2
                    null = null_map(null, psi, mass, gamma)
                    W, a = W_new, a_new
                score_bound = 544 * n / m
                assert max_score_diff <= score_bound + 1e-9
                assert max_a < 4
                assert max_displacement <= 4 * B * math.sqrt(n) / m + 1e-9
                assert tail_count == T // 2 + 1
                assert np.max(np.abs(sum_score - sum_frozen)) / tail_count <= score_bound + 1e-9
                cases.append({"n": n, "m": m, "T": T, "B": B, "initialization": init,
                    "max_actual_frozen_score_difference": max_score_diff,
                    "proved_score_bound": score_bound,
                    "max_output_norm": max_a,
                    "max_input_displacement": max_displacement,
                    "max_changed_gate_point_pairs": max_changed})
    return {"case_count": len(cases), "cases": cases,
            "scope": "Checks comparison lemmas at finite sizes; T is below the main theorem's conservative threshold."}


def density_and_direction_checks() -> dict:
    rng = np.random.default_rng(538712)
    X = cube(4)
    m = len(X)
    W = X / 2
    psi = np.maximum(X @ W.T, 0) / math.sqrt(m)
    assert np.allclose(np.sum(psi**2, axis=1), 0.5)
    minimum_direction = math.inf
    maximum_log_density_ratio = -math.inf
    maximum_log_det_residual = 0.0
    cases = 0
    for T in (25, 32, 81):
        for B in (1.0, 6.0, 12.0):
            gamma = B / T
            for mode in ("uniform", "point_mass", "irregular"):
                if mode == "uniform":
                    mass = np.ones(len(X)) / len(X)
                elif mode == "point_mass":
                    mass = np.eye(len(X))[3]
                else:
                    mass = rng.dirichlet(np.ones(len(X)))
                for _ in range(4):
                    b0 = rng.normal(size=m)
                    z = b0.copy()
                    J = np.eye(m)
                    logdet_sum = 0.0
                    s = (T + 1) // 2
                    for t in range(s):
                        H = null_hessian(z, psi, mass)
                        eig = np.linalg.eigvalsh(H)
                        assert eig.min() >= -1e-12
                        assert np.trace(H) <= LAMBDA / 4 + 1e-12
                        K = np.eye(m) - gamma * H
                        sign, ld = np.linalg.slogdet(K)
                        assert sign > 0
                        logdet_sum += ld
                        J = K @ J
                        z = null_map(z, psi, mass, gamma)
                    sign, logdet = np.linalg.slogdet(J)
                    assert sign > 0
                    maximum_log_det_residual = max(maximum_log_det_residual, abs(logdet - logdet_sum))
                    ratio_log = -0.5 * (b0 @ b0 - z @ z) - logdet_sum
                    bound = s * gamma * LAMBDA / (4 * (1 - gamma * LAMBDA / 4))
                    assert ratio_log <= bound + 1e-9
                    assert bound <= 225 / 238 + 1e-12
                    maximum_log_density_ratio = max(maximum_log_density_ratio, float(ratio_log))
                    L = T - s
                    Jtail = np.eye(m)
                    avgJ = Jtail.copy()
                    zpos, zneg = z.copy(), -z.copy()
                    sumpos, sumneg = z.copy(), -z.copy()
                    for t in range(L):
                        H = null_hessian(zpos, psi, mass)
                        Jtail = (np.eye(m) - gamma * H) @ Jtail
                        assert np.linalg.norm(Jtail - np.eye(m), 2) <= (t + 1) * gamma * LAMBDA / 4 + 1e-9
                        avgJ += Jtail
                        zpos = null_map(zpos, psi, mass, gamma)
                        zneg = null_map(zneg, psi, mass, gamma)
                        sumpos += zpos
                        sumneg += zneg
                    assert np.max(np.abs(sumpos + sumneg)) < 1e-11
                    avgJ /= L + 1
                    for feat in psi:
                        e = feat / np.linalg.norm(feat)
                        deriv = np.linalg.norm(feat) * e @ avgJ @ e
                        assert deriv >= 5 * math.sqrt(7) / 128 - 1e-9
                        minimum_direction = min(minimum_direction, float(deriv))
                    cases += 1
    return {"case_count": cases, "minimum_checked_directional_derivative": minimum_direction,
            "proved_directional_lower_bound": 5 * math.sqrt(7) / 128,
            "maximum_checked_log_density_ratio": maximum_log_density_ratio,
            "proved_log_density_ratio_upper_bound": 225 / 238,
            "max_log_determinant_chain_residual": maximum_log_det_residual}


def main() -> None:
    result = {"status": "all diagnostic assertions passed",
              "interpretation": "Exact rational constant checks and finite floating-point diagnostics; no formal proof verification or learning experiment.",
              "constants": constants(), "analytic_grids": analytic_grids(),
              "trajectories": trajectory_checks(),
              "density_and_direction": density_and_direction_checks()}
    path = Path(__file__).with_name("verification_results.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "trajectory_cases": result["trajectories"]["case_count"],
                      "density_cases": result["density_and_direction"]["case_count"],
                      "results": str(path)}, indent=2))


if __name__ == "__main__":
    main()
