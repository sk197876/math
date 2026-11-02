(** Federer (1969), 2.10.47, p. 204: choose a compact unit cube C with
    positive measure of A intersect C. For compact A, a finite cover by open
    half-radius balls gives such a cube. This makes the initial choice
    explicit without introducing a countable lattice or assuming local
    finiteness of the measure. Source context: DyadicCubeGridUP.v. The
    finite-subcover argument is general topology. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCoordinateMetric CoveringFamilyUP MetricClosedBalls CompactFiniteCover
  MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [compact_positive_unit_cube]: the initial
    positive unit cube in 2.10.47, p. 204.
    The supporting assertion is valid for any outer
    measure, including infinite values, and also in
    ambient dimension zero. *)
Theorem compact_positive_unit_cube (R : realType) n
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure mu -> compact A -> 0<mu A ->
  exists a : R_n R n, 0<mu (A `&` [set y | forall i, (a i<=y i<=a i+1)%R]).
Proof.
move=> hm hA hpos.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose C (x : X) := [set y : X | forall i, (x i-1/2<=y i<=x i-1/2+1)%R].
pose U (x : X) := metric_open_ball x (1/2)%R.
have hhalf : (0<1/2 :> R)%R by lra.
have hUC x : U x `<=` C x.
  move=> y hy i.
  have hc := @euclidean_coordinate_nonexpanding R n i x y.
  rewrite real_line_metric_distanceE in hc.
  have hh : (`|x i-y i|<1/2)%R := le_lt_trans hc hy.
  rewrite ltr_norml in hh; have /andP [hl hu] := hh; apply/andP; split; lra.
have hcover : A `<=` \bigcup_(x in setT) U x.
  move=> x hx; exists x=> //; change (is_true (mdist x x<1/2)%R).
  by rewrite mdistxx.
have [F hF hFA] := @compact_open_finite_cover X X setT U A hA
  (fun x _=>@metric_open_ball_open R X x (1/2)%R) hcover.
have hex : exists x, x \in F /\ 0<mu (A `&` C x).
  apply: contrapT=> hno.
  have hz x (hx : x \in F) : mu (A `&` C x)=0.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
    apply/negP=> hp; apply: hno; by exists x.
  have hc : A `<=` \bigcup_(x in [set` F]) (A `&` C x).
    move=> y hy; have [x hx hxy] := hFA y hy; exists x=> //; split=> //; exact: hUC x y hxy.
  have hh := @measure_indexed_cover R X X mu hm A [set` F] (fun x=>A `&` C x)
    (finite_set_countable (finite_fset F)) hc.
  rewrite (nonnegative_sum_zero hz) in hh.
  have hbad := lt_le_trans hpos hh; by rewrite ltxx in hbad.
have [x [hx hp]] := hex.
exists ([ffun i=>x i-1/2]%R : R_n R n).
have he : [set y : X | forall i, (([ffun i=>x i-1/2] : R_n R n) i<=y i<=
    ([ffun i=>x i-1/2] : R_n R n) i+1)%R]=C x.
  by apply/seteqP; split=> y hy i; have hh := hy i; rewrite !ffunE in hh *.
rewrite -he in hp; exact hp.
Qed.
