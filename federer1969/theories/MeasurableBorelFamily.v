(** Federer (1969), 2.2.1, p. 60: the measurable sets of a measure form a
    Borel family. This follows from the local closure proofs of 2.1.3,
    without an external measure library. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSplit MeasureFiniteClosure
  MeasureCountableClosure BorelFamilyUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_measurable_borel_family]: Federer
    2.2.1, p. 60: all measurable sets form a Borel family
    relative to the measured space. The three closure conditions
    are exactly the previously proved 2.1.3 laws. *)
Theorem measure_measurable_borel_family (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) :
  is_borel_family setT (measure_measurable mu).
Proof.
constructor.
- exact: measure_measurable_empty hm.
- by move=> A _ x _.
- move=> A hA; rewrite setTD; exact: measure_measurable_complement hA.
- move=> G hG hc; exact: (@measure_measurable_countable_union R I _ mu hm G (fun A => A) hc hG).
- move=> G hG hc _; exact: (@measure_measurable_countable_intersection R I _ mu hm G (fun A => A) hc hG).
Qed.

(** Source for [open_measurable_implies_borel_measurable]: Federer
    2.2.1, p. 60, supporting consequence of minimality and the
    measurable Borel family: measurability of every open set implies
    measurability of every Borel set, as used in 2.2.2, pp. 60-61. *)
Theorem open_measurable_implies_borel_measurable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  (forall U, open U -> measure_measurable mu U) ->
  forall B, borel_set B -> measure_measurable mu B.
Proof.
move=> ho; exact: (@generated_borel_family_least _ setT (@open T) _
  (borel_sets_specification T) _ (measure_measurable_borel_family hm) ho).
Qed.
