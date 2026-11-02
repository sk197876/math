(** Federer (1969), 3.2.32, pp. 269–270: supporting
    restrictions to finite measurable source pieces when applying
    3.2.22. The Borel sandwich is 2.2.3, p. 61;
    finite measurability is required before any null difference. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureRestriction MeasureNullModification BorelRegularMeasureUP
  BorelRegularSandwich BorelRegularRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regular_finite_measurable_restriction]: supporting
    source restriction for Federer 3.2.32, pp. 269–270,
    by the finite Borel sandwich in 2.2.3, p. 61.
    A measurable finite-mass restriction is Borel regular.
    The proof uses equal whole restricted measures, justified
    by an actual null difference. It does not assert this
    difference null for a nonmeasurable source. *)
Theorem borel_regular_finite_measurable_restriction (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_borel_regular_measure mu) (A:set X):
  measure_measurable mu A ->mu A< +oo ->is_borel_regular_measure (measure_restrict mu A).
Proof.
move=>hA hFinite.
have [D [B [hD [hB [hDA [hAB hNull]]]]]]:=@borel_regular_finite_sandwich R X mu hm hr A hA hFinite.
have hMeasures:measure_restrict mu A=measure_restrict mu D.
  apply:funext=>Z; apply:(@measure_null_modification_value R X mu hm
    (A `&` Z) (D `&` Z) (B `\` D) hNull)=>x hNot.
  split.
  - move=>[hx hZ]; split=>//.
    case:(pselect (D x))=>hDx; first exact hDx.
    exfalso; apply:hNot; split=>//; exact:hAB.
  - by move=>[hx hZ]; split=>//; exact:hDA.
rewrite hMeasures; exact (borel_regular_restrict_borel hm hr hD).
Qed.
