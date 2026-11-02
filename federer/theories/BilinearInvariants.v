(** Federer (1969), 1.7.10, p. 35: discriminant and trace of a bilinear
    form, defined as determinant and trace of its uniquely characterised
    endomorphism. We formalise the book's scalar-valued definition *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP LinearBasis Hom
  ExteriorDeterminant TraceDefinition BilinearRepresentativeUP BilinearRepresentativeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Invariants.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variables B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [bilinear_representative]: Federer 1.7.10,
    p. 35, the unique endomorphism represented by the given bilinear
    form and inner product, obtained from its sealed interface. *)
Definition bilinear_representative := @BilinearRepresentative.map R V B S hB hS n e he.

(** Source for [bilinear_representativeP]: Federer 1.7.10,
    p. 35, the representative satisfies B(f(x),y)=S(x,y). *)
Theorem bilinear_representativeP : is_bilinear_representative B S bilinear_representative.
Proof. exact: BilinearRepresentative.laws. Qed.

(** Source for [bilinear_discriminant]: Federer 1.7.10,
    p. 35, first defining equation: discr(S) is the determinant
    of the associated endomorphism. *)
Definition bilinear_discriminant : R := det h2 he bilinear_representative.

(** Source for [bilinear_trace]: Federer 1.7.10,
    p. 35, second defining equation: trace(S) is the trace
    of the associated endomorphism. *)
Definition bilinear_trace : R := @trace_Hom R h2 V (Finite.clone 'I_n _) e he
  (hom_of_linear bilinear_representative).

(** Source for [bilinear_discriminant_characterisation]: Federer
    1.7.10, p. 35, the defining determinant can be computed
    with any endomorphism satisfying the characterising equation. *)
Theorem bilinear_discriminant_characterisation (f : {linear V -> V}) :
  is_bilinear_representative B S f -> bilinear_discriminant = det h2 he f.
Proof.
move=> hf; apply: det_ext.
exact (@bilinear_representative_unique R V B S hB bilinear_representative f bilinear_representativeP hf).
Qed.

(** Source for [bilinear_trace_characterisation]: Federer
    1.7.10, p. 35, the defining trace can be computed with
    any endomorphism satisfying the characterising equation. *)
Theorem bilinear_trace_characterisation (f : {linear V -> V}) :
  is_bilinear_representative B S f -> bilinear_trace =
    @trace_Hom R h2 V (Finite.clone 'I_n _) e he (hom_of_linear f).
Proof.
move=> hf.
have hm : hom_of_linear bilinear_representative = hom_of_linear f.
  apply: hom_ext => x; exact (@bilinear_representative_unique R V B S hB
    bilinear_representative f bilinear_representativeP hf x).
by rewrite /bilinear_trace hm.
Qed.
End Invariants.
