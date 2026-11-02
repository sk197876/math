(** Federer (1969), 3.2.3(2), pp. 243–244: the
    bounded Jacobian preserves integrability in the signed
    characteristic-approximation argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness LipschitzUP NormDifferentialLipschitzBound LinearJacobianSandwich
  Jacobian EuclideanJacobianMeasurable PartialFunctionUP PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_jacobian_global_upper_bound]: the
    norm bound J_m Df <= M^m underlying Federer 3.2.3(2),
    p. 243, by 1.7.6 and the directional differential bound.
    It holds at every actual Jacobian graph point. *)
Lemma euclidean_jacobian_global_upper_bound (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (M:R):
  (0<=M)%R -> is_metric_lipschitz_bound setT f M ->
  forall x j,partial_function_graph (extended_euclidean_jacobian f) x j -> j<=(M^+m)%:E.
Proof.
move=>hM hLip x j [r [hr <-]].
have [D [hD hrJ]]:=(euclidean_jacobian_graph m setT f x r).1 hr.
have hUpper:forall v,(inner_norm (@euclidean_inner_productP R n) (D v)<=
    M*inner_norm (@euclidean_inner_productP R m) v)%R.
  apply:(@norm_differential_global_lipschitz_bound R _ _ _ _
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) f x D M hD).
  move=>z w; exact (hLip.2 z w I I).
have hLower v:(0%R*inner_norm (@euclidean_inner_productP R m) v<=
    inner_norm (@euclidean_inner_productP R n) (D v))%R.
  rewrite mul0r; exact:inner_norm_nonnegative.
rewrite -hrJ lee_fin; exact ((euclidean_top_jacobian_sandwich (lexx 0%R) hM hLower hUpper).2).
Qed.
