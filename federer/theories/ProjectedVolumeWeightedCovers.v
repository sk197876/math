(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting
    fractional-cover inequality for the Gross projected-volume gauge of
    2.10.4(1), p. 172. Weighted pointwise domination passes to every
    orthogonal projection; integrate the projected characteristic sum, then
    take the projection supremum. Borel-image measurability is the proved
    2.2.13, pp. 69–70. This is an intermediate estimate, not the final
    weighted-integral equality or an additional assertion attributed to
    2.10.8. no identical Gross weighted theorem was located. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  OrthogonalEuclidean CoordinateProjection EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability
  ProjectionMultiplicityIntegral ProjectedVolumeGaugeUP ProjectedVolumeGauge TopologicalBorel
  NonnegativeSum NonnegativeSumSupport WeightedMetricEnvelopeUP WeightedImageThresholdBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_weighted_cover_threshold]: supporting
    individual-projection estimate for the final paragraph
    of 2.10.24, p. 188. Every Borel image is
    Lebesgue measurable by 2.2.13; projections and
    members may overlap and masses may be infinite. *)
Theorem projection_weighted_cover_threshold (R : realType) (n m : nat) (J : choiceType)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (G : set J) (u : J -> R) (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) (t : R) :
  countable G -> (forall j, G j -> (0<=u j)%R) -> borel_set A ->
  (forall j, G j -> borel_set (S j)) -> (0<=t)%R ->
  (forall x, A x -> t%:E<=weighted_generator_sum S G u x) ->
  t%:E*projected_volume_function (m:=m) A p<=
    nonnegative_sum G (fun j=>(u j)%:E*projected_volume_function (m:=m) (S j) p).
Proof.
move=> hG hu hA hS ht hdom.
exact: (@weighted_image_threshold_bound R (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R m)) J (@euclidean_lebesgue_measure R m)
  (euclidean_projection_linear p) S G u A t (@euclidean_lebesgue_is_measure R m) hG hu
  (@euclidean_projection_borel_image_measurable R n m p A hA)
  (fun j hj=>@euclidean_projection_borel_image_measurable R n m p (S j) (hS j hj)) ht hdom).
Qed.

(** Source for [projected_volume_scaled_least_bound]: supporting
    positive finite scaling of the projection supremum
    in 2.10.4(1), p. 172, used by the
    weighted Gross estimate in 2.10.24, p. 188. *)
Lemma projected_volume_scaled_least_bound (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (t : R) (B : \bar R) :
  (0<t)%R ->
  (forall p : {linear R_n R n -> R_n R m}, O_star p -> t%:E*euclidean_lebesgue_measure m (p @` A)<=B) ->
  t%:E*projected_volume_gauge m A<=B.
Proof.
move=> ht hbound.
have hti : 0<=(t^-1)%R%:E by rewrite lee_fin invr_ge0; exact: ltW ht.
have ht0 : 0<=t%:E by rewrite lee_fin; exact: ltW ht.
have htne : (t!=0)%R by rewrite gt_eqF.
have hcap : projected_volume_gauge m A<=(t^-1)%R%:E*B.
  apply: projected_volume_gauge_least_bound=> p hp.
  have hh := lee_wpmul2l hti (hbound p hp).
  by rewrite muleA -EFinM mulVf // mul1e in hh.
have hh := lee_wpmul2l ht0 hcap.
by rewrite muleA -EFinM mulfV // mul1e in hh.
Qed.

(** Source for [projected_volume_gauge_weighted_cover]: supporting
    fractional-cover estimate for the Gross application
    in 2.10.24, p. 188. Borel targets and
    cover members retain arbitrary countable families,
    finite nonnegative coefficients, positive real
    thresholds and infinite gauge values. This does
    not yet assert the final integral equality. *)
Theorem projected_volume_gauge_weighted_cover (R : realType) (n m : nat) (J : choiceType)
    (S : J -> set (inner_metric_space (@euclidean_inner_productP R n)))
    (G : set J) (u : J -> R) (A : set (inner_metric_space (@euclidean_inner_productP R n))) (t : R) :
  (m<=n)%N -> countable G -> (forall j, G j -> (0<=u j)%R) -> borel_set A ->
  (forall j, G j -> borel_set (S j)) -> (0<t)%R ->
  (forall x, A x -> t%:E<=weighted_generator_sum S G u x) ->
  t%:E*projected_volume_gauge m A<=nonnegative_sum G (fun j=>(u j)%:E*projected_volume_gauge m (S j)).
Proof.
move=> hmn hG hu hA hS ht hdom.
apply: (@projected_volume_scaled_least_bound R n m A t _ ht)=> p hp.
have [q hq] := @euclidean_projection_linear_complete R n m p hp.
have hfun : (euclidean_projection_linear q : R_n R n -> R_n R m)=p by apply: funext.
have hh := @projection_weighted_cover_threshold R n m J S G u A q t hG hu hA hS (ltW ht) hdom.
rewrite /projected_volume_function hfun in hh; apply: le_trans hh _.
apply: nonnegative_sum_mono=> j hj; apply: lee_wpmul2l.
- by rewrite lee_fin; exact: hu.
- exact: (@projected_volume_gauge_projection_bound R n m (S j) p hp).
Qed.
