(** Federer (1969), 3.2.6, p. 246: finite
    multiplicity on a compact scalar source interval.
    This is the already proved 2.10.13 consequence,
    with H^1 on the scalar line identified with L^1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground LocallyAbsolutelyContinuousCurve CurveFiniteMultiplicity
  HausdorffMeasure HausdorffLength HausdorffLengthCompatibility HausdorffLengthReal
  MeasureAlmostUP MappingMultiplicity LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_hausdorff_one_lebesgue]: the n=1
    target measure in Federer 3.2.6, p. 245,
    by H^1=L^1 of 2.10.7, p. 175. *)
Lemma scalar_hausdorff_one_lebesgue (R:realType):
  @hausdorff_measure R [the metricType R of real_line_metric R] 1=@lebesgue_scalar_measure R.
Proof.
apply:funext=>A; rewrite hausdorff_measure_one_length.
by rewrite hausdorff_length_real_eq_lebesgue.
Qed.

(** Source for [scalar_interval_multiplicity_finite]: the
    first almost-everywhere condition in the proof of
    Federer 3.2.6, p. 246. Local absolute continuity
    makes the containing interval variation finite. *)
Lemma scalar_interval_multiplicity_finite (R:realType) (f:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> (a<b)%R ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set y|@mapping_multiplicity R [the choiceType of real_line_metric R] R f `[a,b] y< +oo].
Proof.
move=>hAC hab.
have hFinite:=absolutely_continuous_interval_multiplicity_finite hAC hab.
by rewrite scalar_hausdorff_one_lebesgue in hFinite.
Qed.
