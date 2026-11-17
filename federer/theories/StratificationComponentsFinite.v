(** Federer (1969), 3.4.8(11), pp. 327,
    333–335: the union of the finite
    strata has finitely many components.
    Apply the independent stratification laws and
    the existing finite component-cover assembly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP AnalyticFiniteStratificationUP FiniteComponentCoverAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_union_finite_components]:
    the finite component conclusion assembled
    over all original strata, supporting
    3.4.8(11), pp. 327, 333–335. *)
Theorem analytic_stratification_union_finite_components (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    m (U0 S0:set (R_n R n)) mu (V S G:'I_mu->set (R_n R n)):
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G ->
  finite_set (@connected_component
    (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _)
    (\bigcup_i S i) @` (\bigcup_i S i)).
Proof.
move=>hStrata.
pose T:=Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _.
apply:(@finite_component_cover_assembly T 'I_mu setT S (\bigcup_i S i)).
- exact:finite_finset.
- move=>i _;exact:analytic_stratification_components hStrata i.
- move=>i _ x hx;by exists i.
- move=>x [i _ hi];by exists i;split.
Qed.
