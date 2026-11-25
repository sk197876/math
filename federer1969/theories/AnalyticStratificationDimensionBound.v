(** Federer (1969), corrected 3.4.8(11), p. 327:
    a stratification at a smaller dimension bound
    also satisfies every law at a larger bound.
    The actual strata, neighbourhoods and analytic
    boundary varieties remain the same. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP AnalyticFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_dimension_bound]:
    the smaller-dimensional induction families fit
    the common original bound m in
    corrected 3.4.8(11), p. 327. *)
Theorem analytic_stratification_dimension_bound (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    m M (U0 S0:set (R_n R n)) mu (V S G:'I_mu->set (R_n R n)):
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G ->
  (m<=M)%N ->
  @is_analytic_finite_stratification R n alpha beta M U0 S0 mu V S G.
Proof.
move=>hStrat hBound;constructor.
- exact:analytic_stratification_neighbourhoods hStrat.
- exact:analytic_stratification_germ hStrat.
- move=>i;have [d [hD hFunctional]]:=analytic_stratification_functional hStrat i.
  exists d;split;[exact:leq_trans hD hBound|exact:hFunctional].
- exact:analytic_stratification_components hStrat.
- exact:analytic_stratification_disjoint hStrat.
- exact:analytic_stratification_boundary hStrat.
- exact:analytic_stratification_boundary_analytic hStrat.
- move=>i;have [hEmpty|hDimension]:=analytic_stratification_boundary_dimension hStrat i.
  + by left.
  + right;exact:leq_trans hDimension hBound.
- exact:analytic_stratification_boundary_earlier hStrat.
Qed.
