(** Federer (1969), 3.1.7, p. 217: a differential of
    a global extension is an approximate differential of its restriction
    at a point where the missing domain has density zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP RealMetricBackground
  EuclideanLebesgueDimensions EuclideanClosedBallVolume EuclideanNoncenteredVitali CenteredBallRelations
  MetricClosedBalls PartialFunctionUP MeasureSetDensity CenteredNullSetDensity
  EuclideanZeroDensityUnion LocalZeroDensity EuclideanApproximateContext
  NormDifferentialUP ApproximateDifferentialUP ApproximateDifferentialRemainder
  ApproximateDifferentialAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [ordinary_differential_on_density_domain]: the
    first inference after applying Rademacher's theorem in Federer
    3.1.7, p. 217. The actual restricted domain and
    puncture remain in the quotient. Positive source dimension
    makes the puncture Lebesgue null. *)
Theorem ordinary_differential_on_density_domain (R : realType) m
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (A : set (R_n R m.+1)) (f g : R_n R m.+1->Y)
    (a : R_n R m.+1) (L : Hom (R_n R m.+1) Y) :
  (forall x, A x -> f x=g x) -> A a ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R m.+1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)])
      (~` A)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m.+1))
    NY setT g a L ->
  has_approximate_differential NY A f a L.
Proof.
move=> hfg ha hA hD; split=> // W hW.
pose X := inner_metric_space (@euclidean_inner_productP R m.+1).
pose NX := inner_norm (@euclidean_inner_productP R m.+1).
pose mu := @euclidean_lebesgue_measure R m.+1.
pose V := @centered_closed_ball_relation R [the metricType R of X].
have hz : partial_function_graph (measure_set_density mu V [set a]) a 0%E.
  apply: (@centered_null_set_density_zero R [the metricType R of X]
    mu [set a] a (euclidean_lebesgue_is_measure R m.+1)).
  - move=> x r hr; split; first exact: euclidean_closed_ball_positive.
    by rewrite /mu (euclidean_closed_ball_normalized_volume x (ltW hr)) fin_numE.
  - exact: positive_euclidean_singleton_null.
have hbad := euclidean_zero_density_union hA hz.
have [e he heW] := (metricType_numDomainType.nbhs_mdistP
  (0 : real_line_metric R) W).1 hW.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [d [hd hrem]] := norm_differential_remainder hD he2.
apply: (@local_zero_density_mono R [the metricType R of X] mu V _
  ((~` A) `|` [set a]) [set x | mdist (a : X) x<d] a
  (euclidean_approximate_context R m.+1) (metric_open_ball_open _ _) _ _ hbad).
- change (is_true (mdist (a : X) a<d)).
  by rewrite mdistxx.
- move=> x hx hnot; apply: contrapT=> hnone.
  have hAx : A x by apply: contrapT=> hn; apply: hnone; left.
  have hxa : x!=a by apply/eqP=> h; apply: hnone; right; exact h.
  have hdist : NX (x-a)<d.
    change (is_true (mdist (a : X) x<d)) in hx.
    move: hx; rewrite inner_metric_distanceE -opprB inner_normN; by [].
  have hinc : a+(x-a)=x by rewrite addrC subrK.
  have hbound := hrem (x-a) Logic.I hdist.
  rewrite hinc -(hfg x hAx) -(hfg a ha) in hbound.
  have hp : 0<NX (x-a) by rewrite /NX inner_norm_gt0 subr_eq0.
  pose q := NY (f x-f a-L (x-a))/NX (x-a).
  have hq0 : 0<=q.
    exact: divr_ge0 (real_seminorm_nonnegative hNY.1 _) (ltW hp).
  have hq : q<=e/2 by rewrite /q ler_pdivrMr.
  apply: hnot; exists q; split.
  + apply: (approximate_remainder_quotient_graph NY A f a L x q).2.
    by split=> //; split.
  + apply: heW.
    change (is_true (`|0-q|<e)).
    rewrite sub0r normrN ger0_norm //.
    have hh : e/2<e by lra.
    exact: le_lt_trans hq hh.
Qed.
