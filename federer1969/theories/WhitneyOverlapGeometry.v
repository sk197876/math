(** Federer (1969), 3.1.14, p. 226:
    the distance inequalities between a point x of U
    at distance at most 1/4 from a point a of A, its
    nearest point xi(x), and the centres s of S_x together
    with their nearest points xi(s). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP InnerNearestUP MetricClosedBalls
  MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceBasic
  FedererCoverRadius LipschitzRadiusOverlap EuclideanPartitionBallCoverUP
  WhitneyNearestCenters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OverlapGeometry.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable A : set X.
Hypothesis hA : closed A.
Hypothesis hne : A !=set0.
Variable xi : X->X.
Hypothesis hxi : forall s, is_inner_nearest (@euclidean_inner_productP R m) s A (xi s).
Local Notation Phi := ([set (~` A : set X)]).
Local Notation U := (\bigcup_(T in Phi) T).
Local Notation h := (federer_cover_radius Phi).
Variable S : set X.
Hypothesis hS : is_federer_partition_ball_cover Phi S.
Local Notation Sx := (fun x=>lipschitz_radius_overlap S h 10 10 x).

(** Source for [whitney_three_point_inequality]:
    the triangle inequality |p-q|<=|p-r|+|r-q| used
    repeatedly on Federer 3.1.14, p. 226. *)
Lemma whitney_three_point_inequality (p q r : X) : N (p-q)<=N (p-r)+N (r-q).
Proof.
have -> : p-q=(p-r)+(r-q) by rewrite addrA subrK.
exact: (real_seminorm_triangle hN.1).
Qed.

(** Source for [whitney_nearest_distance]:
    |s-xi(s)|=dist(s,A), Federer 3.1.14, p. 225,
    with the sealed distance function. *)
Lemma whitney_nearest_distance (x : X) : N (x-xi x)=MetricSetDistance.value hne x.
Proof.
have hd := MetricSetDistance.laws hne.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (metric_set_distance_greatest hd)=>a ha.
  rewrite inner_metric_distanceE; exact: (inner_nearest_minimal_law (hxi x) ha).
- have hl := metric_set_distance_lower hd x (inner_nearest_member_law (hxi x)).
  by rewrite inner_metric_distanceE in hl.
Qed.

(** Source for [whitney_nearest_bound]:
    the nearest point is at most as far as any point
    of A, Federer 3.1.14, pp. 225–226. *)
Lemma whitney_nearest_bound (x a : X) : A a -> N (x-xi x)<=N (x-a).
Proof. move=>ha; exact: (inner_nearest_minimal_law (hxi x) ha). Qed.

(** Source for [whitney_nearest_positive]:
    a point of U=R^m-A has positive distance from its
    nearest point of A, Federer 3.1.14, p. 226. *)
Lemma whitney_nearest_positive (x : X) : U x -> 0<N (x-xi x).
Proof.
move=>[T -> hx].
rewrite lt_def (real_seminorm_nonnegative hN.1) andbT; apply/eqP=>h0.
have hz := hN.2 _ h0.
have hxA : A x by rewrite (subr0_eq hz); exact: (inner_nearest_member_law (hxi x)).
exact: (hx hxA).
Qed.

(** Source for [whitney_radius_identity]:
    20h(x)=dist(x,A) whenever dist(x,A)<=1,
    from 20h(x)=inf{1,dist(x,A)}, Federer 3.1.14, p. 225. *)
Lemma whitney_radius_identity (x : X) : N (x-xi x)<=1 -> 20*h x=N (x-xi x).
Proof.
move=>hle; rewrite (whitney_cover_radius_formula hne x) -whitney_nearest_distance.
exact: (min_r hle).
Qed.

(** Source for [whitney_center_in_domain]:
    the selected centres lie in U, Federer 3.1.13,
    p. 224, as used on 3.1.14, p. 226. *)
Lemma whitney_center_in_domain (s : X) : S s -> U s.
Proof. move=>hs; exact: (partition_ball_centers_in_domain hS hs). Qed.

(** Source for [whitney_overlap_radius]:
    h(s)<=3h(x) for s in S_x, Federer 3.1.14, p. 226,
    from the ratio bound of 3.1.13. *)
Lemma whitney_overlap_radius (x s : X) : U x -> Sx x s -> h s<=3*h x.
Proof.
move=>hx hs.
have hpos : 0<h s.
  apply: (federer_cover_radius_positive (Phi:=Phi) (x:=s)).
  - by move=>T ->; exact: closed_openC.
  - have [T hT hsT] := whitney_center_in_domain hs.1; by exists T.
have hratio := (andP (partition_ball_radius_ratios hS hx hs)).1.
rewrite ler_pdivlMr // in hratio; lra.
Qed.

(** Source for [whitney_overlap_center_distance]:
    |s-x|<=10h(s)+10h(x) for s in S_x, Federer 3.1.14,
    p. 226, from the definition of S_x in 3.1.13. *)
Lemma whitney_overlap_center_distance (x s : X) : Sx x s -> N (s-x)<=10*h s+10*h x.
Proof.
move=>[_ [z [hxz hsz]]].
rewrite /metric_closed_ball /= !inner_metric_distanceE in hxz hsz.
have htri := whitney_three_point_inequality s x z.
rewrite (real_seminorm_subtract hN.1 z x) in htri; lra.
Qed.

(** Source for [whitney_nearest_geometry]:
    for a in A and x in U with |x-a|<=1/4 and b=xi(x):
    |x-b|<=|x-a|, 20h(x)=|x-b| and |b-a|<=2|x-a|,
    Federer 3.1.14, p. 226, with |x-b|>0 since x is not in A. *)
Theorem whitney_nearest_geometry (a x : X) : A a -> U x -> N (x-a)<=1/4 ->
  0<N (x-xi x) /\ N (x-xi x)<=N (x-a) /\ 20*h x=N (x-xi x) /\ N (xi x-a)<=2*N (x-a).
Proof.
move=>ha hx hxa.
have hpos := whitney_nearest_positive hx.
have hle := whitney_nearest_bound x ha.
have hrad : 20*h x=N (x-xi x) by apply: whitney_radius_identity; lra.
split; first exact hpos; split; first exact hle; split; first exact hrad.
have htri := whitney_three_point_inequality (xi x) a x.
rewrite (real_seminorm_subtract hN.1 (xi x) x) in htri; lra.
Qed.

(** Source for [whitney_overlap_geometry]:
    for a in A, x in U with |x-a|<=1/4, b=xi(x) and s in S_x:
    20h(s)=|s-xi(s)|, |s-x|<=40h(x)=2|x-b|, |xi(s)-a|<=2 and
    |xi(s)-b|<=6|x-b|, Federer 3.1.14, p. 226. *)
Theorem whitney_overlap_geometry (a x s : X) : A a -> U x -> N (x-a)<=1/4 -> Sx x s ->
  20*h s=N (s-xi s) /\ N (s-x)<=2*N (x-xi x) /\ N (xi s-a)<=2 /\
  N (xi s-xi x)<=6*N (x-xi x).
Proof.
move=>ha hx hxa hs.
have [hpos [hle [hrad hba]]] := whitney_nearest_geometry ha hx hxa.
have hhs := whitney_overlap_radius hx hs.
have hsx := whitney_overlap_center_distance hs.
have hsU := whitney_center_in_domain hs.1.
have hformula : 20*h s=Num.min 1 (N (s-xi s)).
  by rewrite (whitney_cover_radius_formula hne s) -whitney_nearest_distance.
have hd1 : N (s-xi s)<=1.
  rewrite leNgt; apply/negP=>hgt.
  rewrite (min_l (ltW hgt)) in hformula; lra.
have hrads : 20*h s=N (s-xi s) by rewrite hformula (min_r hd1).
split; first exact hrads.
split; first lra.
have ht1 := whitney_three_point_inequality (xi s) a s.
have ht2 := whitney_three_point_inequality s a x.
have ht3 := whitney_three_point_inequality (xi s) (xi x) s.
have ht4 := whitney_three_point_inequality s (xi x) x.
rewrite (real_seminorm_subtract hN.1 (xi s) s) in ht1 ht3.
split; lra.
Qed.
End OverlapGeometry.
