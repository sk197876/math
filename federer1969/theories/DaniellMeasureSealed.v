(** Opaque representing-measure interface for Federer (1969), 2.5.2, pp.
    92–93. Source context, abstract laws and the nonempty-case convention:
    DaniellMeasureUP.v. The implementation is selected only from the proved
    existence result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP DaniellMeasureUP DaniellMeasureConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type DaniellMeasureSignature.
(** Source for [value]: the representing measure promised by Federer 2.5.2,
    p. 92 *)
Parameter value : forall (R : realType) (X : choiceType) (L : set (X -> R)) (A : (X -> R) -> R),
  is_function_lattice L -> is_monotone_daniell_integral L A -> set X -> \bar R.
(** Source for [laws]: abstract measure, representation and
    nonempty-envelope laws proved in Federer 2.5.2, pp. 92–93 *)
Parameter laws : forall (R : realType) (X : choiceType) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A),
  is_monotone_daniell_measure L A (@value R X L A hL hA).
End DaniellMeasureSignature.
Module DaniellMeasure : DaniellMeasureSignature.
(** Source for [value]: private selection of the existence
    witness proved for Federer 2.5.2, pp. 92–93. *)
Definition value (R : realType) (X : choiceType) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A) :=
  projT1 (cid (@monotone_daniell_measure_exists R X L A hL hA)).
(** Source for [laws]: the selected witness satisfies all
    laws for Federer 2.5.2, pp. 92–93. *)
Lemma laws (R : realType) (X : choiceType) (L : set (X -> R)) (A : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_monotone_daniell_integral L A) :
  is_monotone_daniell_measure L A (@value R X L A hL hA).
Proof. exact: projT2 (cid (@monotone_daniell_measure_exists R X L A hL hA)). Qed.
End DaniellMeasure.
