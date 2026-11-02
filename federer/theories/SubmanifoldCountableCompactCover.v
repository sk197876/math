(** Federer (1969), 3.2.28(4), pp. 266–267:
    the finite-dimensional manifold in the area argument
    admits a countable compact cover, by its local
    compactness in 3.1.19, p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormMetricScaleContinuity NormRetractionLocalCompact EuclideanSubmanifoldUP
  SubmanifoldLocalGeometry MetricClosedBalls EuclideanLebesgueHaar CountableCompactNeighbourhoodCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_countable_compact_cover]:
    supporting compact exhaustion for the unrestricted
    manifold B in Federer 3.2.28(4), pp. 266–267.
    Compact balls are supplied by local coordinate
    retractions, then the ambient countable base selects
    a countable cover. No global closedness or finite
    Hausdorff measure of B is assumed. *)
Theorem submanifold_countable_compact_cover (R:realType) n mu k
    (B:set (R_n R n)):
  @is_euclidean_submanifold R n mu k B ->
  exists K:nat->set (R_n R n),
    (forall i,@compact [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)] (K i) /\K i `<=` B) /\
    B=\bigcup_i K i.
Proof.
move=>hB.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=real_norm_metric_space hNX.
have [U hU]:=euclidean_countable_open_base R n.
apply:(@countable_compact_neighbourhood_cover [the topologicalType of X] B U hU).
move=>b hb.
have [T [rho [hTb hRet]]]:=@submanifold_local_retractions R n mu k B hB b hb.
have [r [hr hCompact]]:=@norm_local_retraction_compact_ball R (R_n R n) NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) B T rho k b hTb hRet.
pose V:set X:=[set x|mdist b x<r].
pose K:set (R_n R n):=[set x|B x /\NX (x-b)<=r].
have hId:continuous (fun x:M=>(x:X)).
  apply:(@metric_fixed_lipschitz_continuous R M X _ 1 ler01)=>x y.
  change (is_true (NX (x-y)<=1*NX (x-y))).
  by rewrite mul1r.
have hK:@compact [the topologicalType of X] K.
  have h:=continuous_compact (continuous_subspaceT hId) hCompact.
  by rewrite image_id in h.
exists V,K; split; first exact:metric_open_ball_open.
split.
- change (is_true (mdist (b:X) b<r)); by rewrite mdistxx.
- split; first exact hK.
  split; first by move=>x hx; exact hx.1.
  move=>x [hx hNear]; split; first exact hx.
  have h: NX (x-b)<r.
    change (is_true (@mdist R X b x<r)) in hNear.
    by rewrite metric_sym inner_metric_distanceE in hNear.
  exact:ltW h.
Qed.
