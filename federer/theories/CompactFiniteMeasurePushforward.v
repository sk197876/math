(** Federer (1969), 4.1.5, p. 350:
    localize the original Radon measure to a
    compact neighbourhood before applying 2.8.18
    and 2.9.8. The finite image measure
    is Borel regular by the already proved
    compact-support pushforward theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasurePushforward BorelRegularMeasureUP
  BorelRegularRestriction TopologicalBorel CompactSupportedPushforwardRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_finite_continuous_pushforward]: the
    finite compact localization used for the
    original ball formula, Federer 4.1.5,
    p. 350. No finite total-mass premise
    is imposed on the original measure. *)
Theorem compact_finite_continuous_pushforward (R:realType) (X:metricType R) (Y:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_borel_regular_measure mu)
    (K:set X) (f:X->Y):
  hausdorff_space Y ->compact K ->(mu K< +oo)%E ->continuous f ->
  is_measure (measure_pushforward f (measure_restrict mu K)) /\
  is_borel_regular_measure (measure_pushforward f (measure_restrict mu K)) /\
  (measure_pushforward f (measure_restrict mu K) setT< +oo)%E.
Proof.
move=>hY hK hFinite hF.
have hRestricted:=measure_restrict_is_measure hm K.
have hBorel:borel_set K:=closed_borel_set (compact_closed (@metric_hausdorff R X) hK).
have hRegular:=borel_regular_restrict_borel hm hr hBorel.
have hTotal:(measure_restrict mu K setT< +oo)%E by rewrite /measure_restrict setIT.
have hOutside:measure_restrict mu K (~` K)= 0%E.
  by rewrite /measure_restrict setICr (measure_empty hm).
split; first exact:measure_pushforward_is_measure.
split.
- exact:(@compact_supported_continuous_pushforward_borel_regular R X Y
    (measure_restrict mu K) hRestricted hRegular K f hY hK hF hTotal hOutside).
- by rewrite /measure_pushforward preimage_setT.
Qed.
