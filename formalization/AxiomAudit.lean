import GaussianSGD

/-! `#print axioms` for every theorem that corresponds to a statement in the paper. -/

-- Initialization bounds (`lem:init`)
#print axioms GaussianSGD.init_hidden
#print axioms GaussianSGD.init_output
-- Score comparison through gate changes (`lem:score`)
#print axioms GaussianSGD.score_comparison
#print axioms GaussianSGD.tail_score_comparison
-- Sampling and label effects (`lem:population`)
#print axioms GaussianSGD.g_bsign
#print axioms GaussianSGD.Pmap_eq_mean
#print axioms GaussianSGD.Rmap_neg
#print axioms GaussianSGD.Rmap_nonexpansive
#print axioms GaussianSGD.Pmap_nonexpansive
#print axioms GaussianSGD.sample_nonexpansive
#print axioms GaussianSGD.frozen_sq_error
#print axioms GaussianSGD.label_effect
#print axioms GaussianSGD.tail_sq_error
#print axioms GaussianSGD.tail_label_effect
-- Density at the beginning of the tail (`lem:density`)
#print axioms GaussianSGD.density_bound
-- Anti-concentration of the symmetric tail (`lem:smallball`)
#print axioms GaussianSGD.smallball
#print axioms GaussianSGD.null_risk
-- Kernel facts used in `thm:risk` and `cor:parity`
#print axioms GaussianSGD.Phi_norm_sq
#print axioms GaussianSGD.kernelCorr_eq_norm
#print axioms GaussianSGD.kernel_identity
#print axioms GaussianSGD.integrable_norm_mu
#print axioms GaussianSGD.kernelCorr_parity_sq_le
-- Convex separation and ordinary dimension (`lem:geometry`)
#print axioms GaussianSGD.margin_and_vc
#print axioms GaussianSGD.growth_bound
-- Risk controlled by kernel correlation (`thm:risk`)
#print axioms GaussianSGD.cond_risk_lower
#print axioms GaussianSGD.risk_lower_bound
#print axioms GaussianSGD.lossTerm_regime
#print axioms GaussianSGD.risk_lower_bound_regime
-- Kernel margin from success under every marginal (`thm:margin`)
#print axioms GaussianSGD.kernel_margin
#print axioms GaussianSGD.lossTerm_le_half
#print axioms GaussianSGD.regime_of_large
#print axioms GaussianSGD.kernel_margin_regime
-- Parity obstruction (`cor:parity`)
#print axioms GaussianSGD.parity_lower_bound
-- Fixed gates at small total step (`thm:gate`, `lem:rows`)
#print axioms GaussianSGD.row_movement
#print axioms GaussianSGD.exact_representation
#print axioms GaussianSGD.gateSet_mass
#print axioms GaussianSGD.gateBound_le
#print axioms GaussianSGD.gate_pdc
#print axioms GaussianSGD.gate_small_step
