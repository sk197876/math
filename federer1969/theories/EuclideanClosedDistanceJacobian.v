(** Federer (1969), 3.2.34, p. 271: the actual
    differential of the distance has degree-one Jacobian
    one at every differentiability point outside the
    original nonempty closed set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  InnerNormInequalities RealNormUP NormDifferentialUP NormDifferentialLipschitzBound
  EuclideanOneCoordinate EuclideanOneNormDifferential MetricSetDistanceUP MetricSetDistanceBasic
  MetricNearestSegment NormRayDifferentialValue EuclideanClosedDistanceNearest
  EuclideanDistanceLipschitz EuclideanLinearJacobian EuclideanUnitDirectionJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_closed_distance_jacobian_one]:
    Df(x)(s-x)=-|s-x| and J_1 f(x)=1 in
    Federer 3.2.34, p. 271. A local nearest
    point gives the exact one-sided increment; the
    actual differential and the global Lipschitz bound
    give matching bounds for its exterior norm.
    No derivative field, convexity, boundedness or
    positive-mass hypothesis is added. *)
Lemma euclidean_closed_distance_jacobian_one (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d x
    (L:Hom (R_n R n) (R_n R 1)):
  closed S ->S!=set0 ->is_metric_set_distance S d ->~S x ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R 1)) setT
    (fun z=>euclidean_one_embed (d z)) x L ->
  euclidean_linear_jacobian 1 L= 1.
Proof.
move=>hClosed hNonempty hDistance hx hD.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hOne:=inner_norm_real_norm (@euclidean_inner_productP R 1).
have [s [hs hNearest]]:=euclidean_closed_distance_nearest x hClosed hNonempty hDistance.
pose v:=s-x.
have hv:v!=0.
  apply/negP=>/eqP he; apply:hx.
  have hEq:s=x by apply/eqP; rewrite -subr_eq0; apply/eqP; exact he.
  by rewrite -hEq.
have hp:0<N v by rewrite (real_norm_positive hN.1 hN.2).
have hRay (t:R):0<=t<=1 ->
    euclidean_one_embed (d (x+t*:v))=euclidean_one_embed (d x)+
      t*:(euclidean_one_embed (-N v)).
  move=>ht.
  have hh:=@norm_nearest_segment_distance R (R_n R n) N hN S d x s t
    (euclidean_distance_norm_laws hDistance) hs hNearest ht.
  rewrite hh; apply/ffunP=>i.
  rewrite /euclidean_one_embed !ffunE.
  change (d x-t*N (s-x)=d x+t*(-N v)).
  by rewrite mulrN.
have hValue:=@norm_differential_from_ray_increment R (R_n R n) (R_n R 1)
  N (inner_norm (@euclidean_inner_productP R 1)) hN hOne setT
  (fun z=>euclidean_one_embed (d z)) x L v (euclidean_one_embed (-N v)) hD hRay.
apply:(euclidean_unit_direction_jacobian (w:=v)).
- move=>z.
  have hBound:=@norm_differential_global_lipschitz_bound R (R_n R n) (R_n R 1)
    N (inner_norm (@euclidean_inner_productP R 1)) hN hOne
    (fun z=>euclidean_one_embed (d z)) x L 1 hD.
  have hPair u w:inner_norm (@euclidean_inner_productP R 1)
      (euclidean_one_embed (d u)-euclidean_one_embed (d w))<=1*N (u-w).
    by rewrite mul1r; exact:(euclidean_distance_norm_lipschitz hDistance u w).
  have hh:=hBound hPair z.
  by rewrite mul1r in hh.
- exact hp.
- rewrite hValue euclidean_one_norm_coordinate /euclidean_one_embed ffunE normrN.
  exact:(ger0_norm (ltW hp)).
Qed.
