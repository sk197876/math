(** Federer (1969), 3.3.19, p. 305: the actual
    original radial values in every late tail are dense
    in the actual unit circle, on one common conull set. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric CircularDiscTreeUP CircularDiscLimitUP
  CircularDiscRadialMapUP CircularDiscRadialMapLaws CircularDiscLateArcVisits CircularRationalArcBasis
  PartialFunctionUP PlanarUnitCircleGeometry HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Tails.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_radial_tail]: the actual
    original set {eta_n(a):n>v} in 3.3.19,
    p. 305. No auxiliary total extension is used. *)
Definition circular_disc_radial_tail (eta:nat->partial_function E E) (x:E) v:set E:=
  [set y:E|exists j:nat,(v<j)%N /\partial_function_graph (eta j) x y].

Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.
Variable eta:nat->partial_function E E.
Hypothesis hEta:forall j,is_circular_disc_radial_map H j (eta j).

(** Source for [circular_disc_visitor_tails_dense]: actual
    radial values at a common rational-arc visitor have
    every late tail dense in the original S^1. The
    rational arc basis and original unit-range laws discharge
    both closure inclusions, supporting 3.3.19, p. 305. *)
Theorem circular_disc_visitor_tails_dense (x:E):
  A x ->is_circular_late_arc_visitor eta x ->forall v,
    closure (circular_disc_radial_tail eta x v)= @planar_unit_circle R.
Proof.
move=>hxA hVisits v.
have hSubset:circular_disc_radial_tail eta x v `<=` @planar_unit_circle R.
  move=>y [j [hj hGraph]].
  exact:(@circular_disc_radial_map_unit R H hH j (eta j) (hEta j) x y hGraph).
apply/seteqP;split.
- move=>y hy.
  have hClosure:= @closureS E (circular_disc_radial_tail eta x v) (@planar_unit_circle R) hSubset y hy.
  by rewrite -((@closure_id E (@planar_unit_circle R)).1 (@planar_unit_circle_closed R)) in hClosure.
- move=>y hy U hU.
  have [e he hBall]:=(proj1 (metricType_numDomainType.nbhs_mdistP y U)) hU.
  have [a [b [ha [hab [hb hArc]]]]]:= @circular_rational_arc_ball_basis R y e hy he.
  have [j [z [hj [hGraph hInArc]]]]:= hVisits a b ha hab hb v.+1.
  exists z;split.
  + exists j;by split.
  + exact:hBall z (hArc z hInArc).
Qed.

(** Source for [circular_disc_angular_tails_dense_almost]:
    for H1 almost all original a in A, the original
    sets {eta_n(a):n>v} are dense in S^1 for every
    integer v, exactly 3.3.19, p. 305. Actual
    exceptional-set contraction, countable assembly, exact
    domains, unit values and the circle basis are proved. *)
Theorem circular_disc_angular_tails_dense_almost:
  measure_almost_everywhere_on (@hausdorff_measure R E 1) A
    [set x:E|forall v,closure (circular_disc_radial_tail eta x v)= @planar_unit_circle R].
Proof.
have hAlmost:= @circular_disc_late_rational_arc_visits_almost R H hH A hA eta hEta.
have hMu:= @hausdorff_measure_is_measure R E 1.
have hAbsolute:=(@measure_almost_everywhere_on_implication R E (@hausdorff_measure R E 1) A _).1 hAlmost.
apply:(@measure_almost_everywhere_on_implication R E (@hausdorff_measure R E 1) A _).2.
apply:(@measure_almost_everywhere_mono R E (@hausdorff_measure R E 1) hMu _ _ _ hAbsolute).
move=>x hGood hxA;exact:(@circular_disc_visitor_tails_dense x hxA (hGood hxA)).
Qed.
End Tails.
