(** Supporting finite-dimensional topology for Federer (1969), 2.10.5(2), p.
    173, and 3.2.36, p. 272. Linear maps between Euclidean spaces of
    different dimensions are continuous by the actual operator norm of
    1.7.6, pp. 33–34. This expands the finite-dimensional continuity
    background of 1.7.1, p. 28; no external linear-continuity theorem
    replaces the norm argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerNorm OperatorNormUP OperatorNorm NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rectangular_euclidean_linear_continuous]:
    supporting continuous section maps for Federer
    2.10.5(2), p. 173. Use the norm bound
    |f(x)-f(y)|<=||f|| |x-y| proved from
    1.7.6, pp. 33–34. Either dimension may
    be zero. *)
Theorem rectangular_euclidean_linear_continuous (R : realType) (n m : nat)
    (f : {linear R_n R n -> R_n R m}) :
  continuous (f : inner_metric_space (@euclidean_inner_productP R n) ->
    inner_metric_space (@euclidean_inner_productP R m)).
Proof.
pose hB := @euclidean_inner_productP R n.
pose hC := @euclidean_inner_productP R m.
pose L := linear_operator_norm hB hC (@coordinate_basisP R n) f.
have hL : 0<=L := linear_operator_norm_nonnegative hB hC (@coordinate_basisP R n) f.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ L hL)=> x y.
rewrite !inner_metric_distanceE -linearB.
exact: linear_operator_norm_bound.
Qed.
