(** Federer (1969), 1.6.6, p. 26, and 3.4.12, p. 339:
    conjugation is the original scalar ring automorphism. Package
    its proved addition and product laws for the inverse-coordinate
    coefficients in the unitary primitive-direction argument. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Conjugation.
Variable R:realFieldType.
Local Notation C:=(ComplexScalars.C R).
(** Source for [complex_conjugation_function]: the original
    conjugation from 1.6.6, p. 26; no representation is opened. *)
Definition complex_conjugation_function:C->C:=@conjugate R.
(** Source for [complex_conjugation_additive]: conjugation preserves
    zero and sums, 1.6.6, p. 26. *)
Lemma complex_conjugation_additive:nmod_morphism complex_conjugation_function.
Proof.
split;last exact:conjugate_add.
change (conjugate (0:C)=0).
by rewrite -(rmorph0 (ComplexScalars.embed R)) conjugate_real.
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build C C
  complex_conjugation_function complex_conjugation_additive.
(** Source for [complex_conjugation_multiplicative]: conjugation
    preserves one and products, 1.6.6, p. 26. *)
Lemma complex_conjugation_multiplicative:monoid_morphism complex_conjugation_function.
Proof.
split;last exact:conjugate_mul.
change (conjugate (1:C) = 1).
by rewrite -(rmorph1 (ComplexScalars.embed R)) conjugate_real.
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build C C
  complex_conjugation_function complex_conjugation_multiplicative.
(** Source for [complex_conjugation_morphism]: the original
    conjugation as a ring map, supporting 3.4.12, p. 339. *)
Definition complex_conjugation_morphism:{rmorphism C->C}:=
  GRing.RMorphism.clone C C complex_conjugation_function _.
End Conjugation.
