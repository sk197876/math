(** Federer (1969), 3.1.14, p. 225:
    the nearest points xi(s) in the closed set A and the
    identification 20h(x)=inf{1,dist(x,A)} of the radius of
    3.1.13 for the family consisting of the open complement of A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology ring lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNearestUP CompactNearest EuclideanClosedBallCompact MetricClosedBalls
  MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceBasic MetricSetDistanceClosure
  TruncatedComplementDistanceUP TruncatedComplementDistanceSealed TruncatedComplementDistanceLaws
  OpenCoverClearanceUP OpenCoverClearanceSealed OpenCoverClearanceLaws FedererCoverRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NearestCenters.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Variable A : set X.
Hypothesis hA : closed A.
Hypothesis hne : A !=set0.

(** Source for [whitney_nearest_point_exists]:
    "For each s in S we choose xi(s) in A with
    |s-xi(s)|=dist(s,A)", Federer 3.1.14, p. 225.
    A nearest point exists in every nonempty closed
    subset of R^m, since its intersection with a
    closed ball is compact. *)
Theorem whitney_nearest_point_exists (s : X) :
  exists xi, is_inner_nearest (@euclidean_inner_productP R m) s A xi.
Proof.
have [a0 ha0] := hne.
pose K := A `&` metric_closed_ball s (mdist s a0).
have hK0 : K !=set0.
  by exists a0; split; [exact ha0|rewrite /metric_closed_ball /= lexx].
have hKc : compact K.
  apply: (subclosed_compact (B:=metric_closed_ball s (mdist s a0))).
  - exact: (closedI hA (@metric_closed_ball_closed R X s (mdist s a0))).
  - exact: (@euclidean_closed_metric_ball_compact R m s (mdist s a0)).
  - by move=>x [_ hx].
have [c hc] := compact_inner_nearest_exists s hK0 hKc.
exists c; split; first exact: (inner_nearest_member_law hc).1.
move=>x hx; case: (pselect (metric_closed_ball s (mdist s a0) x))=>[hxb|hxb].
- exact: (inner_nearest_minimal_law hc (conj hx hxb)).
- have hfar : mdist s a0<mdist s x by rewrite ltNge; apply/negP.
  have ha0K : K a0 by split; [exact ha0|exact: lexx].
  have hca0 : N (s-c)<=N (s-a0) := inner_nearest_minimal_law hc ha0K.
  change (is_true (N (s-a0)<N (s-x))) in hfar.
  exact: (le_trans hca0 (ltW hfar)).
Qed.

(** Source for [whitney_cover_radius_formula]:
    "apply 3.1.13 with Phi={U}, so that 20h(x)=inf{1,dist(x,A)}
    for x in U", Federer 3.1.14, p. 225. The identity
    holds for every x of R^m, with the sealed distance
    to A; the singleton family has the single open
    member U=R^m-A. *)
Theorem whitney_cover_radius_formula x :
  20*federer_cover_radius [set (~` A : set X)] x=
    Num.min 1 (MetricSetDistance.value hne x).
Proof.
have hlaws := OpenCoverClearance.laws [set (~` A : set X)].
have htcd := TruncatedComplementDistance.laws (~` A : set X).
have hdist : is_metric_set_distance (~` (~` A)) (MetricSetDistance.value hne).
  by rewrite setCK; exact: MetricSetDistance.laws.
have hvalue : OpenCoverClearance.value [set (~` A : set X)] x=
    TruncatedComplementDistance.value (~` A : set X) x.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: (open_cover_clearance_least hlaws).
    + exact: (truncated_complement_distance_nonnegative htcd x).
    + by move=>T ->.
  - exact: (open_cover_clearance_upper hlaws x (erefl _)).
rewrite /federer_cover_radius hvalue (truncated_complement_distance_minimum htcd hdist x).
by field.
Qed.
End NearestCenters.
