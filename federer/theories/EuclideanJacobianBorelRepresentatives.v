(** Federer (1969), 3.2.22, p. 259: exact
    Borel nonnegative representatives of the two ordinary
    scalar Jacobians in the target-chart factorization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LipschitzUP EuclideanLinearJacobian EuclideanJacobianContinuity
  EuclideanTargetJacobianContinuity EuclideanDifferentialBorelRepresentative
  BorelFunctionUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_target_jacobian_borel_representative_exists]:
    supporting scalar J_mu phi_ij in Federer 3.2.22,
    p. 259. A Borel representative agrees with
    every actual target-degree Jacobian and is nonnegative
    everywhere, including its auxiliary undefined-point defaults. *)
Lemma euclidean_target_jacobian_borel_representative_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  exists J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R,
    is_borel_function J /\ (forall x,0<=J x) /\
    forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
      J x=euclidean_linear_jacobian n D.
Proof.
move=>hLip; exact:(@euclidean_nonnegative_differential_borel_representative R m n f
  (fun D=>euclidean_linear_jacobian n D) hLip (@euclidean_target_jacobian_continuous R m n)
  (fun D=>@euclidean_linear_jacobian_nonnegative R m n n D)).
Qed.

(** Source for [euclidean_top_jacobian_borel_representative_exists]:
    supporting scalar J_mu gamma_j in Federer 3.2.22,
    p. 259. Exact Borel values permit composition
    with phi_ij before the local integral comparison.
    This uses the top-source Jacobian continuity and
    does not replace its actual partial domain. *)
Lemma euclidean_top_jacobian_borel_representative_exists (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)):
  is_metric_lipschitz setT f ->
  exists J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R,
    is_borel_function J /\ (forall x,0<=J x) /\
    forall x D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D ->
      J x=euclidean_linear_jacobian m D.
Proof.
move=>hLip; exact:(@euclidean_nonnegative_differential_borel_representative R m n f
  (fun D=>euclidean_linear_jacobian m D) hLip (@euclidean_top_jacobian_continuous R m n)
  (fun D=>@euclidean_linear_jacobian_nonnegative R m n m D)).
Qed.
