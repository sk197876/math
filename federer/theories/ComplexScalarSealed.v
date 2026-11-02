(** Federer (1969), 1.6.6, pp. 26-27: scalar background for the comparison
    of real and complex forms. Only this existence witness imports
    MathComp's construction of complex numbers. Downstream arguments use the
    sealed scalar laws, not that construction or its exterior-algebra or
    determinant results. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarUP.
From mathcomp Require Import complex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type ComplexScalarSig.
(** Source for [C]: Federer 1.6.6, p. 26, opening paragraph.
    Sealed specification of the complex scalar field over a real field. *)
Parameter C : realFieldType -> fieldType.
(** Source for [embed]: Federer 1.6.6, p. 26, underlying real space.
    Sealed specification of the real scalar embedding. *)
Parameter embed : forall R : realFieldType, {rmorphism R -> C R}.
(** Source for [ii]: Federer 1.6.6, p. 26, real and imaginary parts.
    Sealed specification of the imaginary unit. *)
Parameter ii : forall R : realFieldType, C R.
(** Source for [re]: Federer 1.6.6, p. 26, real and imaginary parts.
    Sealed specification of the real coordinate. *)
Parameter re : forall R : realFieldType, C R -> R.
(** Source for [im]: Federer 1.6.6, p. 26, real and imaginary parts.
    Sealed specification of the imaginary coordinate. *)
Parameter im : forall R : realFieldType, C R -> R.
(** Source for [laws]: Federer 1.6.6, p. 26, scalar background.
    Sealed specification; the following implementation proves all laws. *)
Parameter laws : forall R : realFieldType,
  is_complex_scalar_system (embed R) (ii R) (@re R) (@im R).
End ComplexScalarSig.

Module ComplexScalars : ComplexScalarSig.
(** Source for [C]: Federer 1.6.6, p. 26, scalar background.
    Existence witness for the complex scalar field. *)
Definition C (R : realFieldType) : fieldType :=
  GRing.Field.clone (complex.complex R) _.
(** Source for [embed]: Federer 1.6.6, p. 26, scalar background.
    Existence witness for the real scalar embedding. *)
Definition embed (R : realFieldType) : {rmorphism R -> C R} :=
  GRing.RMorphism.clone _ _ (complex.real_complex R) _.
(** Source for [ii]: Federer 1.6.6, p. 26, scalar background.
    Existence witness for the imaginary unit. *)
Definition ii (R : realFieldType) : C R := @complex.Complex R 0 1.
(** Source for [re]: Federer 1.6.6, p. 26, scalar background.
    Existence witness for the real coordinate. *)
Definition re (R : realFieldType) (z : C R) : R := complex.Re z.
(** Source for [im]: Federer 1.6.6, p. 26, scalar background.
    Existence witness for the imaginary coordinate. *)
Definition im (R : realFieldType) (z : C R) : R := complex.Im z.
(** Source for [laws]: Federer 1.6.6, p. 26, scalar background.
    Verification of the abstract scalar laws for the existence witness. *)
Lemma laws (R : realFieldType) :
  is_complex_scalar_system (embed R) (ii R) (@re R) (@im R).
Proof.
constructor; try by [].
- by move=> [a b] [c d].
- by move=> [a b] [c d].
- by move=> a [x y] /=; rewrite mul0r subr0.
- by move=> a [x y] /=; rewrite mul0r addr0.
- by move=> [x y] /=; congr (complex.Complex _ _);
    rewrite ?mul0r ?mul1r ?subr0 ?sub0r ?addr0 ?add0r.
- by change (@complex.Complex R (0 * 0 - 1 * 1) (0 * 1 + 1 * 0) =
      complex.Complex (-1) (-0));
    congr (complex.Complex _ _); rewrite ?mul0r ?mul1r ?sub0r ?addr0 ?oppr0.
Qed.
End ComplexScalars.
