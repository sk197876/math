(** Federer (1969), 3.2.38, pp. 274--275: the auxiliary
    scalar representative has the actual partial Jacobian graph value
    at every genuine differentiability point used in the core. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  NormDifferentialUP EuclideanLinearJacobian EuclideanJacobianMeasurable Jacobian PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [jacobian_representative_actual_graph]: supporting
    the good-core subset integrals in Federer 3.2.38, p. 275.
    The representative agrees with every actual differential's
    source-degree Jacobian, hence its value is an actual extended
    Jacobian graph value. No default outside that domain is used. *)
Lemma jacobian_representative_actual_graph (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->R) a:
  (forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
    J x=euclidean_linear_jacobian m D) ->
  (exists D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a D) ->
  partial_function_graph (extended_euclidean_jacobian f) a (J a)%:E.
Proof.
move=>hJ [D hD]; exists (J a); split; last reflexivity.
apply:(euclidean_jacobian_graph m setT f a _).2.
exists D; split; first exact hD; symmetry; exact:hJ a D hD.
Qed.
