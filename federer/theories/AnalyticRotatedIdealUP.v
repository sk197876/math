(** Federer (1969), 3.4.8(2), p. 326:
    the original ideal I_g is the image under the
    actual orthogonal germ homomorphism. Independent membership
    laws precede existence and sealing. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_ideal_image]: the original
    membership equation for I_g in 3.4.8(2), p. 326,
    stated for a ring map before applying it to the
    actual orthogonal germ action. It asserts no ideal
    closure or Borel theorem. *)
Definition is_analytic_ideal_image (A B:comNzRingType) (M:{rmorphism A->B})
    (I:set A) (J:set B):Prop:=
  forall beta,J beta <->exists alpha,I alpha /\M alpha=beta.
