(** Federer (1969), 3.3.19, p. 304:
    the actual convex boundary pays the complete
    finite point-weight budget. The boundary parameter
    and its finite ordering are constructed locally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  CoveringFamilyUP LipschitzUP LipschitzCurveAbsoluteContinuity LocallyAbsolutelyContinuousCurve
  ConvexBoundaryCircularCurve FiniteClosedCurveWeightBudget SimpleClosedCurveLength
  CircularTrigonometrySealed CircularTrigonometryUP RealTrigonometryUP
  CurveVariationUP HausdorffMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_boundary_finite_weight_budget]:
    the last finite cyclic inequality of 3.3.19,
    p. 304, for arbitrary original nonempty
    bounded open convex S. Distinct selected boundary
    points have the stated pair-weight distance bound;
    a locally constructed simple closed boundary curve
    and a proved finite sorting argument discharge
    the ordering and perimeter comparison. *)
Theorem convex_boundary_finite_weight_budget (R:realType) (I:finType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (zeta:I->inner_metric_space (@euclidean_inner_productP R 2)) (w:I->R):
  S!=set0 ->open S ->is_inner_convex S ->metric_set_bounded S ->
  (2<=#|I|)%N ->(forall i,(closure S `\` interior S) (zeta i)) ->
  (forall i j,i!=j ->w i+w j<=mdist (zeta i) (zeta j)) ->
  ((2*(\sum_i w i))%:E<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
      (closure S `\` interior S))%E.
Proof.
move=>hNonempty hOpen hConvex hBound hCard hBoundary hPair.
pose E:= inner_metric_space (@euclidean_inner_productP R 2).
pose p:= @CircularTrigonometry.half_period R.
have hp:0<p:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hPeriodPositive:0<2* p by lra.
have [C [L [hL [hLipschitz [hPeriod [hInjective hImage]]]]]]:=
  @convex_boundary_circular_curve_exists R S hNonempty hOpen hConvex hBound.
have hParameters i:exists t:R,(0<=t /\t<2* p) /\C t= zeta i.
  have hi:= hBoundary i;rewrite -hImage in hi.
  have [t ht hValue]:= hi.
  exists t;split=>//;move:ht;rewrite /= in_itv /= =>/andP[ht0 htP];by split.
have [t hT]:= choice hParameters.
have hEndpoints:C 0= C (2* p).
  have hOld:= hPeriod 0.
  have hAngle:0+(@CircularTrigonometry.half_period R+@CircularTrigonometry.half_period R)= 2* p by rewrite /p;ring.
  by rewrite hAngle in hOld;exact:esym hOld.
have hC:continuous (C:real_line_metric R->E).
  apply:locally_absolutely_continuous_curve_continuous.
  apply:(@metric_lipschitz_curve_locally_absolute_continuous R [the metricType R of E] C L).
  split=>//;by move=>x y _ _;exact:hLipschitz.
have hInjectiveOn:{in (`[0,2* p[:set R) &,injective C}.
  move=>a b;rewrite !inE /= !in_itv /= =>/andP[ha haP] /andP[hb hbP].
  exact:hInjective.
have hClosedImage:C @` (`[0,2* p]:set R)= closure S `\` interior S.
  rewrite -hImage;apply/seteqP;split=>y.
  - move=>[u hu hValue];move:hu;rewrite /= in_itv /= =>/andP[hu0 huP].
    case:(ltP u (2* p))=>hStrict.
    + exists u=>//;by rewrite /= in_itv /= hu0 hStrict.
    + have hEnd:u= 2* p by lra.
      exists 0;first by rewrite /= in_itv /= lexx hPeriodPositive.
      by rewrite hEndpoints -hEnd.
  - move=>[u hu hValue];exists u=>//.
    move:hu;rewrite /= !in_itv /= =>/andP[hu0 huP];by rewrite hu0 (ltW huP).
have hLength:= @simple_closed_curve_image_length R [the metricType R of E] C 0 (2* p) hC
  hPeriodPositive hEndpoints hInjectiveOn.
rewrite hClosedImage in hLength.
rewrite hLength.
apply:(@finite_closed_curve_weight_budget R [the metricType R of E] I C t w 0 (2* p) hCard).
- by move=>i;split;[exact:(hT i).1.1|exact:ltW (hT i).1.2].
- exact hEndpoints.
- move=>i j hDifferent;rewrite (hT i).2 (hT j).2;exact:hPair i j hDifferent.
Qed.
