(** Federer (1969), 2.10.21, p. 183: replace C by the net centres whose
    closed epsilon balls meet C; their Hausdorff distance is at most
    epsilon. Nonempty finite sets are consequently dense in F_(a,r). Follow
    the printed hit-set formula and finite-cover proof. No bounded
    compactness is needed once the target C is compact. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground MetricClosedBalls MetricSetDistanceUP MetricSetDistanceBasic
  CompactSetDistanceProfile CompactBallProfiles CompactFiniteCover HausdorffDistanceUP
  HausdorffDistanceBasic HausdorffDistance CompactHausdorffMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_net_hit_set]: direct finite
    approximation Z intersect {z:B(z,epsilon) meets C}
    in 2.10.21, p. 183. *)
Definition finite_net_hit_set (R : realType) (X : metricType R)
    (C Z : set X) (e : R) : set X :=
  [set z | Z z /\ exists x, C x /\ metric_closed_ball z e x].

(** Source for [hausdorff_finite_net_hit_bound]: direct
    Hausdorff bound for the printed hit-set formula
    in 2.10.21, p. 183. Covering C alone
    suffices for this supporting result. *)
Theorem hausdorff_finite_net_hit_bound (R : realType) (X : metricType R)
    (C : compact_metric_set X) (Z : set X) (e : R) :
  finite_set Z -> 0<=e -> val C `<=` \bigcup_(z in Z) metric_closed_ball z e ->
  exists D : compact_metric_set X, val D=finite_net_hit_set (val C) Z e /\ hausdorff_distance C D<=e.
Proof.
move=> hZ he hcover.
pose E := finite_net_hit_set (val C) Z e.
have hEF : finite_set E.
  apply: (sub_finite_set (B:=Z)); last exact hZ.
  by move=> z [hz _].
have hEn : E !=set0.
  have [x hx] := (set_valP C).2.
  have [z hz hzx] := hcover x hx; exists z; split=> //; exists x; by split.
pose D : compact_metric_set X := exist _ E (mem_set (conj (finite_compact hEF) hEn)).
exists D; split; first by [].
apply: (proj2 (hausdorff_distance_directed_bound (@hausdorff_distance_specification R X) C D he)).
split=> x hx.
- have [z hz hzx] := hcover x hx.
  have hzD : val D z by split=> //; exists x; by split.
  apply: le_trans (@metric_set_distance_lower R X (val D) (compact_set_distance_profile D)
    (compact_set_distance_profile_specification D) x z hzD) _.
  by rewrite metric_sym.
- have [hz [y [hy hxy]]] : E x := hx.
  exact: le_trans (@metric_set_distance_lower R X (val C) (compact_set_distance_profile C)
    (compact_set_distance_profile_specification C) x y hy) hxy.
Qed.

(** Source for [compact_hausdorff_finite_approximation]: direct
    finite-set approximation in 2.10.21, p. 183,
    with centres chosen inside C. The resulting
    finite set stays inside every containing ball. *)
Theorem compact_hausdorff_finite_approximation (R : realType) (X : metricType R)
    (C : compact_metric_set X) (e : R) : 0<e ->
  exists D : compact_metric_set X, finite_set (val D) /\ val D `<=` val C /\ hausdorff_distance C D<=e.
Proof.
move=> he.
have hcover : val C `<=` \bigcup_(z in val C) [set x | mdist z x<e].
  move=> x hx; exists x=> //; by rewrite /= mdistxx.
have [Z hZ hcov] := @compact_open_finite_cover X X (val C) (fun z=>[set x | mdist z x<e])
  (val C) (set_valP C).1 (fun z _ => metric_open_ball_open z e) hcover.
have hclosedcover : val C `<=` \bigcup_(z in [set` Z]) metric_closed_ball z e.
  move=> x hx; have [z hz hzx] := hcov x hx; exists z=> //; exact: ltW hzx.
have [D [hD hdist]] := hausdorff_finite_net_hit_bound (finite_fset Z) (ltW he) hclosedcover.
exists D; split.
- rewrite hD; apply: (sub_finite_set (B:=[set` Z])); last exact: finite_fset.
  by move=> x [hx _].
split=> // x hx.
rewrite hD in hx; have hz : x \in Z := hx.1.
exact: set_mem (hZ x hz).
Qed.

(** Source for [finite_compact_sets_dense_in_ball]: direct
    density of nonempty finite sets in F_(a,r),
    2.10.21, p. 183, in the Hausdorff topology.
    The result includes radius zero and arbitrary metric spaces. *)
Theorem finite_compact_sets_dense_in_ball (R : realType) (X : metricType R)
    (a : X) (r : R) (C : compact_hausdorff_space X) :
  compact_sets_in_ball a r C ->
  closure [set D : compact_hausdorff_space X | compact_sets_in_ball a r D /\ finite_set (val D)] C.
Proof.
move=> hC W hW.
have [e he hball] := (metricType_numDomainType.nbhs_mdistP C W).1 hW.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [D [hfin [hDC hdist]]] := compact_hausdorff_finite_approximation C he2.
exists (D : compact_hausdorff_space X); split.
- split=> // x hx; exact: hC x (hDC x hx).
- apply: hball; change (is_true (hausdorff_distance C D<e)).
  apply: le_lt_trans hdist _; by rewrite ltr_pdivrMr ?ltr0n // mulr_natr ltrDl.
Qed.
