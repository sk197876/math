(** Public selected interval constructions for Federer (1969), 2.10.7, pp.
    174–175. Apply the existing sealed general Caratheodory operator to the
    abstract endpoint family and raw increment cost. Nonnegative costs imply
    the approximation measure laws and the final Borel-regularity laws.
    Equality of all positive-cutoff approximations and identification with
    the induced Stieltjes measure are separate consequences, not defining
    premises. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP StieltjesIntervalBounds
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost CaratheodoryMeasure
  CaratheodoryLimitMeasure CaratheodoryBorelRegular MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_caratheodory_scale]: direct
    size-delta approximating measure of Federer
    2.10.7, p. 174, selected through the
    sealed general covering-infimum laws. *)
Definition stieltjes_caratheodory_scale (R : realType) (g : R -> R) (delta : \bar R) :=
  metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta.

(** Source for [stieltjes_caratheodory_scale_specification]:
    abstract covering laws for each size-delta
    approximation in Federer 2.10.7, p. 174. *)
Lemma stieltjes_caratheodory_scale_specification (R : realType) (g : R -> R) (delta : \bar R) :
  is_metric_scale_envelope (@stieltjes_interval_set R) (stieltjes_interval_cost g) delta
    (stieltjes_caratheodory_scale g delta).
Proof. exact: metric_scale_envelope_specification. Qed.

(** Source for [stieltjes_caratheodory_measure]: direct
    final measure of Federer 2.10.7, p. 174,
    selected by the sealed general construction. *)
Definition stieltjes_caratheodory_measure (R : realType) (g : R -> R) :=
  caratheodory_measure (@stieltjes_interval_set R) (stieltjes_interval_cost g).

(** Source for [stieltjes_caratheodory_specification]:
    direct independent interval construction laws
    in Federer 2.10.7, p. 174. *)
Lemma stieltjes_caratheodory_specification (R : realType) (g : R -> R) :
  is_stieltjes_caratheodory_measure g (stieltjes_caratheodory_measure g).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [stieltjes_caratheodory_is_measure]:
    direct final measure assertion of Federer
    2.10.7, p. 174, with the printed
    nondecreasing hypothesis. *)
Lemma stieltjes_caratheodory_is_measure (R : realType) (g : R -> R) :
  (forall a b, a<=b -> g a<=g b) -> is_measure (stieltjes_caratheodory_measure g).
Proof.
move=> hg; exact: caratheodory_limit_is_measure (stieltjes_caratheodory_specification g)
  (stieltjes_interval_cost_nonnegative hg).
Qed.

(** Source for [stieltjes_caratheodory_borel_regular]: supporting Borel
    regularity used to identify the measure in Federer 2.10.7, p. 174, by
    2.10.1, p. 170. *)
Theorem stieltjes_caratheodory_borel_regular (R : realType) (g : R -> R) :
  (forall a b, a<=b -> g a<=g b) ->
  is_borel_regular_measure (stieltjes_caratheodory_measure g).
Proof.
move=> hg; exact: caratheodory_limit_borel_regular (stieltjes_caratheodory_specification g)
  (stieltjes_interval_cost_nonnegative hg) (@stieltjes_interval_borel R).
Qed.
