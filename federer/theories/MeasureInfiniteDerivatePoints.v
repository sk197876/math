(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureDerivates CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_infinite_derivate_points]: supporting
    exceptional set for Federer 2.9.16, p. 161, obtained
    by replacing the centered relation of 2.9.15, p. 160,
    by the displayed relation V. It uses an actual infinite ordinary
    derivate value for the supplied relation. *)
Definition measure_infinite_derivate_points (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) : set X :=
  [set x | partial_function_graph (measure_derivate psi phi V) x +oo].

(** Source for [zero_lower_limit_infinite_derivate_points_empty]:
    supporting inference in Federer 2.9.16, p. 161:
    the everywhere zero lower derivate excludes an infinite
    ordinary derivate at every point. Undefined ordinary
    limits are not assigned values. *)
Lemma zero_lower_limit_infinite_derivate_points_empty (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) :
  (forall x, covering_lower_limit V (measure_ratio_function psi phi) x=0) ->
  measure_infinite_derivate_points psi phi V=set0.
Proof.
move=> hz; apply/seteqP; split=> x; last by move=> [].
move=> [_ [_ hl]]; by move: hl; rewrite (hz x)=> /eqP.
Qed.
