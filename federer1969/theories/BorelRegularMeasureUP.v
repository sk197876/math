(** Federer (1969), 2.2.3, pp. 61-62: Borel regular measures. The measure
    laws remain a separate predicate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RegularMeasureUP TopologicalBorel MeasurableBorelFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_borel_regular_measure]: Federer 2.2.3, p. 61, opening
    definition: open sets are measurable and every subset has a Borel
    superset of equal measure. Direct abstract specification *)
Record is_borel_regular_measure (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) : Prop := {
  borel_regular_open_measurable : forall U, open U -> measure_measurable mu U;
  borel_regular_cover : forall A, exists B,
    A `<=` B /\ borel_set B /\ mu A = mu B
}.

(** Source for [borel_regular_borel_measurable]: Federer 2.2.3, p. 61,
    supporting consequence of the open-set condition and 2.2.1, p. 60. *)
Lemma borel_regular_borel_measurable (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) A : borel_set A -> measure_measurable mu A.
Proof.
exact: (@open_measurable_implies_borel_measurable R T mu hm
  (borel_regular_open_measurable hr) A).
Qed.

(** Source for [borel_regular_is_regular]: Federer 2.2.3, p. 61, supporting
    comparison with regularity in 2.1.5, p. 56: a Borel superset is
    measurable and therefore witnesses ordinary regularity. the converse is
    not asserted. *)
Lemma borel_regular_is_regular (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  is_borel_regular_measure mu -> is_regular_measure mu.
Proof.
move=> hr A; have [B [hAB [hB he]]] := borel_regular_cover hr A.
exists B; split=> //; split=> //.
exact: (@borel_regular_borel_measurable R T mu hm hr B hB).
Qed.
