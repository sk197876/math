(** Federer (1969), 3.2.35, p. 272:
    the boundary of the actual positive tube
    is its entire original distance level. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra num_normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric RealNormUP
  NormSmallStrictContraction MetricSetDistanceUP MetricSetDistanceBasic MetricSetDistanceContinuity
  MetricDistanceClosureLaws EuclideanClosedDistanceNearest EuclideanDistanceTubeBasic RealMetricBackground
  RealOpenIntervals FiniteNormEquivalence HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_tube_closure]:
    supporting closure of the tubes in Federer
    3.2.35, p. 272. Continuity gives the
    closed sublevel inclusion. For equality,
    a nearest point in the source closure
    gives strict contractions with distance below
    r, approaching each level-r point. This
    supporting theorem needs no source convexity,
    boundedness or measurability. *)
Theorem euclidean_distance_tube_closure (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_metric_set_distance S d ->0<r ->
  closure [set x|d x<r]=[set x|d x<=r].
Proof.
move=>hNonempty hD hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose N:=inner_norm (@euclidean_inner_productP R n).
have hDClosure:=metric_distance_closure_laws hD.
have hClosureNonempty:closure S!=set0 by have [a ha]:=hNonempty; exists a; exact:subset_closure ha.
have hClosed:@closed [the topologicalType of X] [set x|d x<=r].
  apply:((@continuous_closedP [the topologicalType of X] [the topologicalType of real_line_metric R] d).1
    (@metric_set_distance_continuous R _ S d hD) [set t|t<=r]).
  exact:closed_le.
have hSubset:[set x|d x<r] `<=` [set x|d x<=r] by move=>x hx; exact:ltW.
apply/seteqP; split=>x.
- move=>hx; exact (hClosed x (@closureS [the topologicalType of X] [set z|d z<r] [set z|d z<=r] hSubset x hx)).
- move=>hx.
  case:(ltP (d x) r)=>[hStrict|hNonStrict].
    exact:(@subset_closure [the topologicalType of X] [set z|d z<r] x hStrict).
  have hValue:d x=r by apply/eqP; rewrite eq_le hx hNonStrict.
  have [a [ha hNearest]]:=@euclidean_closed_distance_nearest R n (closure S) d x
    (@closed_closure [the topologicalType of X] S) hClosureNonempty hDClosure.
  move=>U hU.
  have [eps hEps hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (x:X) U) hU.
  have [s [hs0 [hs1 hNear]]]:=@norm_small_strict_contraction R (R_n R n) N
    (@inner_norm_real_norm R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)) (x-a) eps hEps.
  pose z:=a+s*:(x-a).
  have hLower:=@metric_set_distance_lower R _ (closure S) d hDClosure z a ha.
  have hDifference:z-a=s*:(x-a) by rewrite /z addrAC subrr add0r.
  have hStrict:d z<r.
    apply:(le_lt_trans hLower _).
    change (is_true (N (z-a)<r)).
    rewrite hDifference /N inner_normZ (ger0_norm (ltW hs0)) -hNearest hValue.
    have hProduct:s*r<1*r by rewrite (ltr_pM2r hr).
    by rewrite mul1r in hProduct.
  exists z; split; first exact hStrict; apply:hBall.
  change (is_true (N (x-z)<eps)).
  have hNearDifference:z-x=s*:(x-a)-(x-a) by rewrite /z opprB addrA [s*:(x-a)+a]addrC.
  rewrite -[x-z]opprB /N inner_normN hNearDifference.
  exact hNear.
Qed.

(** Source for [euclidean_distance_tube_boundary]:
    the whole boundary equals d^-1{r} in
    Federer 3.2.35, p. 272. Actual
    strict-sublevel openness and the proved closed
    sublevel identity retain every original level
    point, including exceptional nearest directions.
    No derivative or boundary regularity is assumed. *)
Theorem euclidean_distance_tube_boundary (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_metric_set_distance S d ->0<r ->
  closure [set x|d x<r] `\` interior [set x|d x<r]=[set x|d x=r].
Proof.
move=>hNonempty hD hr.
rewrite (@euclidean_distance_tube_closure R n S d r hNonempty hD hr).
have hOpen:=@euclidean_distance_tube_open R n S d r hD.
apply/seteqP; split=>x.
- move=>[hx hOutside].
  have hNoStrict:~d x<r by move=>hStrict; apply:hOutside; exact:open_nbhs_nbhs (conj hOpen hStrict).
  apply/eqP; rewrite eq_le hx /= leNgt; apply/negP; exact hNoStrict.
- move=>hx; split; first by change (is_true (d x<=r)); rewrite hx.
  move=>hInterior; have hStrict:d x<r:=interior_subset hInterior.
  by rewrite hx ltxx in hStrict.
Qed.
