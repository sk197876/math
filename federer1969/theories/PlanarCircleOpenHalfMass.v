(** Federer 2.10.2(1), p. 171: an open planar set of diameter at most
    the unit circle's diameter contains at most half its actual length.
    The set and its antipodal image are genuinely disjoint; measurability,
    finiteness and antipodal invariance are proved, not extra premises. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  PlanarUnitCircleGeometry HausdorffMeasure HausdorffClosedCoverAgreement
  EuclideanBallVolume MetricDiameter MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_planar_circle_intersection_half_length]: Federer
    2.10.2(1), p. 171; supporting antipodal half-length bound in the
    fixed-cutoff example. The original generator is open with diameter
    at most two; its circle intersection is not assumed measurable. *)
Theorem open_planar_circle_intersection_half_length (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))):
  open S -> extended_metric_diameter S <= (2:R)%:E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (@planar_unit_circle R `&` S) <= (euclidean_unit_ball_volume R 2)%:E.
Proof.
move=>hOpen hDiam.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose mu:=@hausdorff_measure R X 1.
pose A:=@planar_unit_circle R.
pose T:=A `&` S.
pose U:=(fun x:X=> (-x)%R) @` T.
have hm:=@hausdorff_measure_is_measure R X 1.
have hBorel:=@hausdorff_measure_borel_regular R X 1.
have hAM:measure_measurable mu A.
  apply:(borel_regular_borel_measurable hm hBorel).
  apply:closed_borel_set; exact:planar_unit_circle_closed.
have hSM:measure_measurable mu S.
  apply:(borel_regular_borel_measurable hm hBorel); exact:open_borel_set hOpen.
have hTM:measure_measurable mu T:=measure_measurable_intersection hm hAM hSM.
have hNeg:mu U=mu T.
  exact:(@inner_antipodal_hausdorff_invariance R (R_n R 2)
    (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2) 1 T).
have hMass:mu A=(2*euclidean_unit_ball_volume R 2)%R%:E:=planar_unit_circle_length R.
have hSubset:T `<=` A by move=>x [hx _].
have hBound:mu T<=mu A:=measure_mono hm hSubset.
have hFin:mu T \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm T)).
  apply:le_lt_trans hBound _.
  change (mu A < +oo).
  rewrite hMass; exact:ltry.
have hDisjoint:forall x,T x ->U x ->False.
  move=>x [hx hxS] [y [hy hyS] hEq].
  have hNegative:S (-y)%R by rewrite hEq.
  exact:(@open_planar_diameter_two_excludes_antipodes R S y hOpen hDiam hy hyS hNegative).
have hUnion:T `|` U `<=` A.
  move=>x [hx|[y [hy hyS] <-]]; first exact:hx.1.
  change (inner_norm (@euclidean_inner_productP R 2) (-y)%R = 1%R).
  rewrite inner_normN; exact:hy.
have hSum:mu (T `|` U)<=mu A:=measure_mono hm hUnion.
rewrite (@measure_disjoint_union R X mu T U hTM hDisjoint) hNeg hMass
  -(fineK hFin) -EFinD lee_fin in hSum.
change (mu T<=(euclidean_unit_ball_volume R 2)%:E).
rewrite -(fineK hFin) lee_fin.
clear -R hSum; lra.
Qed.
