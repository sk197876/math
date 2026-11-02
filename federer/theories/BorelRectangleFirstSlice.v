(** Federer (1969), 2.10.46, p. 204: supporting Borel measurability of the
    first-factor slice measure. This uses only restriction and image
    measures from 2.1.2, p. 54, and continuous Borel preimages from 2.2.1,
    p. 60. The second factor may be arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MetricProductRectangles MeasureUP MeasureRestriction MeasurePushforward
  PushforwardMeasurableSets BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_rectangle_first_slice_measurable]: supporting
    Borel-set law for the first-factor measure in the
    product argument of 2.10.46, p. 204. Only
    continuity of the first coordinate is needed here. *)
Lemma borel_rectangle_first_slice_measurable (R : realType) (P X Y : topologicalType)
    (first : P -> X) (second : P -> Y) (V : set Y) (mu : set P -> \bar R) :
  is_measure mu -> is_borel_regular_measure mu -> continuous first -> forall U,
  borel_set U -> measure_measurable (fun A=>mu (metric_product_rectangle first second A V)) U.
Proof.
move=> hm hr hc U hU.
have he : (fun A=>mu (metric_product_rectangle first second A V))=
    measure_pushforward first (measure_restrict mu (second @^-1` V)).
  by apply: funext=> A; rewrite /metric_product_rectangle /measure_pushforward /measure_restrict setIC.
rewrite he; apply: pushforward_measurable_from_preimage; apply: measure_restrict_measurable.
apply: (borel_regular_borel_measurable hm hr).
exact (@continuous_borel_preimage P X first hc U hU).
Qed.
