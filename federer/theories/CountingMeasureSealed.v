(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import CountingMeasureUP CountingMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type CountingMeasureSignature.
(** Source for [value]: Federer 2.1.2, p. 54;
    abstract counting measure. *)
Parameter value : forall (R : realType) (I : choiceType), set I -> \bar R.
(** Source for [laws]: Federer 2.1.2, p. 54;
    cardinality specification for the exposed measure. *)
Parameter laws : forall (R : realType) (I : choiceType),
  is_counting_measure (@value R I).
End CountingMeasureSignature.

Module CountingMeasure : CountingMeasureSignature.
(** Source for [value]: Federer 2.1.2, p. 54;
    private choice of an established counting-measure witness. *)
Definition value (R : realType) (I : choiceType) :=
  projT1 (cid (@counting_measure_exists R I)).
(** Source for [laws]: Federer 2.1.2, p. 54;
    chosen witness satisfies the abstract cardinality specification. *)
Lemma laws (R : realType) (I : choiceType) :
  is_counting_measure (@value R I).
Proof. exact: projT2 (cid (@counting_measure_exists R I)). Qed.
End CountingMeasure.
