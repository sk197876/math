(** Federer (1969), 3.2.22, p. 259: Borel
    nonnegative representatives of actual scalar differential
    expressions used in the local chart comparison. Their
    defaults are auxiliary and do not enlarge the public
    differential or approximate-Jacobian domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormMetric EuclideanHomOperator NormDifferentialUP LipschitzUP EuclideanLipschitzClassZero
  EuclideanDifferentialObservables PartialFunctionUP BorelPartialTotalExtension
  InnerOwnNormTopology TopologicalBorel BorelFunctionUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_nonnegative_differential_borel_representative]:
    supporting measurable scalar Jacobians in Federer 3.2.22,
    p. 259. The exact Borel differential domain of
    3.1.1 gives a Borel scalar representative agreeing
    at every actual differentiability point, with zero at
    undefined points. Nonnegativity of the scalar expression
    gives nonnegativity everywhere. No chosen derivative
    field or completed-measure pullback is assumed. *)
Theorem euclidean_nonnegative_differential_borel_representative (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (h:Hom (R_n R m) (R_n R n)->R):
  is_metric_lipschitz setT f ->
  continuous (fun D:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (h D:real_line_metric R)) ->
  (forall D,0<=h D) ->
  exists J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R,
    is_borel_function J /\ (forall x,0<=J x) /\
    forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D ->J x=h D.
Proof.
move=>hLip hCont hNonneg.
pose d:=euclidean_differential_observable f h.
have hBorel (U:set (real_line_metric R)):open U ->
    @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
      (partial_function_preimage d U).
  move=>hU; have hRaw:=euclidean_differential_observable_borel
    (euclidean_lipschitz_norm_class_zero hLip) hCont (open_borel_set hU).
  exact:((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hRaw).
have [J [hExt [hDefault hJ]]]:=@borel_partial_total_extension_exists
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  [the topologicalType of real_line_metric R] d 0 hBorel.
have hActual x D:has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->J x=h D.
  move=>hD; apply:hExt; apply:(euclidean_differential_observable_graph f h x _).2.
  exists D; by split.
exists J; split; first exact hJ; split; last exact hActual.
move=>x; have [hx|hx]:=pselect (partial_function_domain d x).
- have [r hr]:=hx; have [D [hD hValue]]:=(euclidean_differential_observable_graph f h x r).1 hr.
  rewrite (hActual x D hD); exact:hNonneg.
- by rewrite (hDefault x hx).
Qed.
