(** Public measures of Federer (1969), 2.10.4,
    p. 172. The actual projected-volume gauge and
    existing sealed Caratheodory operator give existence;
    results use their abstract specifications. Source
    editions and dimensional scope: ProjectedVolumeGaugeUP.v
    and ProjectionMeasureUP.v. The open/closed convex
    equality and the degree-one identity are separate
    mathematical obligations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric ProjectedVolumeGauge
  ProjectionMeasureUP CaratheodoryMeasure CaratheodoryLimitUP CaratheodoryBorelRegular
  BorelCaratheodoryMeasure CaratheodoryLimitMeasure BorelRegularMeasureUP TopologicalBorel MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [gross_measure]: direct selected Gross
    measure in Federer 2.10.4(1), p. 172. Its
    construction is the sealed Borel-generator specialization
    with the actual projected-volume cost. *)
Definition gross_measure (R : realType) (n m : nat) :=
  borel_caratheodory_measure (@projected_volume_gauge R n m).

(** Source for [gross_measure_specification]: covering laws
    of the measure defined in Federer 2.10.4(1),
    p. 172, proved by the existing sealed general
    construction, rather than an existence premise. *)
Lemma gross_measure_specification (R : realType) (n m : nat) :
  is_gross_measure m (@gross_measure R n m).
Proof. exact: borel_caratheodory_specification. Qed.

(** Source for [gross_measure_is_measure]: measure assertion
    for the Gross construction of Federer 2.10.4(1),
    p. 172. The dimensional premise supplies the
    nonnegative gauge required by 2.10.1. *)
Theorem gross_measure_is_measure (R : realType) (n m : nat) :
  (m<=n)%N -> is_measure (@gross_measure R n m).
Proof.
move=> hmn; exact (@borel_caratheodory_is_measure R
  (inner_metric_space (@euclidean_inner_productP R n)) (@projected_volume_gauge R n m)
  (@projected_volume_gauge_borel_cover_cost R n m hmn)).
Qed.

(** Source for [gross_measure_borel_regular]: supporting
    Borel regularity of the Gross measure in Federer
    2.10.4(1), p. 172, from the Borel-generator
    theorem of 2.10.1, p. 170. *)
Theorem gross_measure_borel_regular (R : realType) (n m : nat) :
  (m<=n)%N -> is_borel_regular_measure (@gross_measure R n m).
Proof.
move=> hmn; exact (@borel_caratheodory_borel_regular R
  (inner_metric_space (@euclidean_inner_productP R n)) (@projected_volume_gauge R n m)
  (@projected_volume_gauge_borel_cover_cost R n m hmn)).
Qed.

(** Source for [caratheodory_projection_measure]: direct
    selected Caratheodory measure in Federer 2.10.4(2),
    p. 172, from open convex generators and the
    actual projected-volume gauge. *)
Definition caratheodory_projection_measure (R : realType) (n m : nat) :=
  caratheodory_measure (fun j : open_convex_euclidean_sets R n => val j)
    (fun j => projected_volume_gauge m (val j)).

(** Source for [caratheodory_projection_measure_specification]:
    proved covering specification for the selected measure
    of Federer 2.10.4(2), p. 172. *)
Lemma caratheodory_projection_measure_specification (R : realType) (n m : nat) :
  is_caratheodory_projection_measure m (@caratheodory_projection_measure R n m).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [caratheodory_projection_measure_is_measure]:
    measure assertion for Federer 2.10.4(2), p. 172,
    from the actual gauge's proved nonnegativity for m<=n. *)
Theorem caratheodory_projection_measure_is_measure (R : realType) (n m : nat) :
  (m<=n)%N -> is_measure (@caratheodory_projection_measure R n m).
Proof.
move=> hmn; apply: (caratheodory_limit_is_measure
  (@caratheodory_projection_measure_specification R n m))=> j.
exact: projected_volume_gauge_nonnegative.
Qed.

(** Source for [caratheodory_projection_measure_borel_regular]:
    supporting Borel regularity of the measure in
    Federer 2.10.4(2), p. 172, since each open
    convex generator is Borel, by 2.10.1, p. 170. *)
Theorem caratheodory_projection_measure_borel_regular (R : realType) (n m : nat) :
  (m<=n)%N -> is_borel_regular_measure (@caratheodory_projection_measure R n m).
Proof.
move=> hmn; apply: (caratheodory_limit_borel_regular
  (@caratheodory_projection_measure_specification R n m)).
- move=> j; exact: projected_volume_gauge_nonnegative.
- move=> j; exact: open_borel_set (set_valP j).1.
Qed.
