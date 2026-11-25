(** Federer (1969), 3.4.12, p. 339: scalar powers retain
    the original geometric bounds in the complex division series.
    Reuse multiplicativity and the original real embedding law. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexModulus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_modulus_power]: the scalar power estimate
    in 3.4.6, p. 323, extended by 3.4.12, p. 339,
    including exponent zero. *)
Lemma complex_modulus_power (R:realType) (z:ComplexScalars.C R) m:
  complex_modulus (z^+m)=(complex_modulus z)^+m.
Proof.
elim:m=>[|m ih];last by rewrite !exprS complex_modulus_mul ih.
have hOne:(1:ComplexScalars.C R)=ComplexScalars.embed R 1 by rewrite rmorph1.
by rewrite !expr0 hOne complex_modulus_real normr1.
Qed.
