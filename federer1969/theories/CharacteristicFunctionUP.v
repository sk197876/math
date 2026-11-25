(** Federer (1969), 2.2.14, p. 70: a characteristic function equals one on
    its set and zero on the complement. The pointwise laws are specified
    before a witness is chosen. Source context: BorelFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_characteristic_function]: direct two-case
    definition in Federer 2.2.14, p. 70. We use a
    real scalar field and abstract pointwise laws; no decision
    procedure for the set is part of the public interface. *)
Record is_characteristic_function (R : realType) (X : Type) (A : set X)
    (f : X -> R) : Prop := {
  characteristic_on_set : forall x, A x -> f x = 1;
  characteristic_off_set : forall x, ~ A x -> f x = 0
}.

(** Source for [characteristic_function_unique]: supporting
    uniqueness for the definition in Federer 2.2.14, p. 70:
    the two pointwise cases determine every value. *)
Lemma characteristic_function_unique (R : realType) (X : Type) (A : set X)
    (f g : X -> R) : is_characteristic_function A f ->
  is_characteristic_function A g -> forall x, f x = g x.
Proof.
move=> hf hg x; case: (pselect (A x))=> hx.
- by rewrite (characteristic_on_set hf hx) (characteristic_on_set hg hx).
- by rewrite (characteristic_off_set hf hx) (characteristic_off_set hg hx).
Qed.
