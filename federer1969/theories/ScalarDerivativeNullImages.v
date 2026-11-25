(** Federer (1969), 3.2.7, p. 246, third
    example: the signed square root preserves null sets.
    This supporting theorem derives that property from
    actual finite derivatives off one point, using the
    countable Lipschitz cover and the project's Hausdorff
    image estimate. It assumes no absolute continuity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP ScalarDifferentiabilityCover LipschitzUP
  HausdorffMeasure HausdorffRestrictedLipschitz HausdorffLengthCompatibility HausdorffLengthReal
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_derivative_off_point_preserves_null_sets]:
    supporting the null-image criterion of 2.10.13 in
    the third example of Federer 3.2.7, p. 246.
    Finite actual derivatives cover every point except
    a fixed singleton, whose image is itself null. *)
Theorem scalar_derivative_off_point_preserves_null_sets (R:realType) (f:R->R) (a:R):
  (forall x,x!=a -> exists v,has_real_curve_derivative f x v) ->
  forall N:set (real_line_metric R),lebesgue_scalar_measure N=0%E ->
    lebesgue_scalar_measure (f @` N)=0%E.
Proof.
move=>hD N hN; have hm:=lebesgue_scalar_is_measure R.
have [F [hF hCover]]:=@scalar_differentiability_lipschitz_cover R f.
pose E q:=N `&` F q.
have hPiece q:lebesgue_scalar_measure (f @` E q)=0%E.
  have hZero:lebesgue_scalar_measure (E q)=0%E.
    exact (@measure_null_subset R [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R) hm
      (E q) N (fun x hx=>hx.1) hN).
  have [L [hL hLip]]:=(hF q).2.
  have hEstimate:=@hausdorff_lipschitz_on_bound R [the metricType R of real_line_metric R]
    [the metricType R of real_line_metric R] (F q) f L 1 (E q) hLip (fun x hx=>hx.2).
  rewrite !hausdorff_measure_one_length !hausdorff_length_real_eq_lebesgue hZero mule0 in hEstimate.
  by apply/eqP; rewrite eq_le hEstimate (measure_nonnegative hm).
have hUnion:lebesgue_scalar_measure (\bigcup_q f @` E q)=0%E.
  exact (measure_null_countable_union hm (countableP _) (fun q _=>hPiece q)).
have hBoth:lebesgue_scalar_measure ([set f a] `|` \bigcup_q f @` E q)=0%E.
  exact (measure_null_union hm (lebesgue_scalar_singleton (f a)) hUnion).
apply:(measure_null_subset hm _ hBoth)=>y [x hx <-].
case:(eqVneq x a)=>[->|hxa]; first by left.
right; have [q _ hqx]:=hCover x (hD x hxa).
exists q; first exact I; exists x; last exact:erefl.
by split.
Qed.
