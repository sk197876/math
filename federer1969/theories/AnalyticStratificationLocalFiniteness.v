(** Federer (1969), 3.4.8(11), p. 333:
    the smaller-dimensional stratification supplies the
    local component count used for the critical
    variety. The actual strata remain inside the
    original analytic representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws AnalyticFiniteStratificationUP
  FiniteStrataLocalComponentFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_local_component_finiteness]:
    apply the finite-stratum component connection directly
    to the independent corrected laws of 3.4.8(11),
    pp. 327, 333. This theorem does not
    assume finiteness of the original representative's
    components, only the proved stratum laws. *)
Theorem analytic_stratification_local_component_finiteness (R:realType) n
    (H U0:set (R_n R n)) m mu (V S G:'I_mu->set (R_n R n)):
  @is_analytic_finite_stratification R n
    (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 H)
    (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0)
    m U0 set0 mu V S G ->
  (forall i,S i `<=` H) ->
  exists U:set (R_n R n),
    @open (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) U /\U 0 /\
    finite_set (@connected_component (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _)
      H @` (H `&` U)).
Proof.
move=>hLaws hSub.
pose T:=Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setC0
  (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setIT in hGerm.
exact:(@finite_strata_local_component_finiteness T 'I_mu 0 H S hSub
  (analytic_stratification_components hLaws) (esym hGerm)).
Qed.
