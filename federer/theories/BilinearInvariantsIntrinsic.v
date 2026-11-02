(** Federer (1969), 1.7.10, p. 35: supporting intrinsicness of the
    discriminant and trace definitions. The finite basis used to prove
    existence of the representing endomorphism must not affect either
    number. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP LinearBasis Hom
  ExteriorDeterminant TraceDefinition GammaIntrinsic BilinearRepresentativeUP BilinearInvariants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Intrinsic.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variables B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Variable n : nat.
Variables e b : 'I_n -> V.
Hypotheses (he : is_basis e) (hb : is_basis b).

(** Source for [bilinear_representative_basis_independent]: Federer
    1.7.10, p. 35, supporting uniqueness independent of the
    basis supplied as a finite-dimensionality witness. *)
Theorem bilinear_representative_basis_independent :
  bilinear_representative hB hS he =1 bilinear_representative hB hS hb.
Proof.
exact (@bilinear_representative_unique R V B S hB
  (bilinear_representative hB hS he) (bilinear_representative hB hS hb)
  (bilinear_representativeP hB hS he) (bilinear_representativeP hB hS hb)).
Qed.

(** Source for [bilinear_discriminant_basis_independent]: Federer
    1.7.10, p. 35, supporting independence of the discriminant
    from the basis used to express the determinant. *)
Theorem bilinear_discriminant_basis_independent :
  bilinear_discriminant h2 hB hS he = bilinear_discriminant h2 hB hS hb.
Proof.
rewrite (@bilinear_discriminant_characterisation R h2 V B S hB hS n e he
  (bilinear_representative hB hS hb) (bilinear_representativeP hB hS hb)).
exact: det_basis_independent.
Qed.

(** Source for [bilinear_trace_basis_independent]: Federer
    1.7.10, p. 35, supporting independence of the bilinear
    trace from the basis used to express the endomorphism trace. *)
Theorem bilinear_trace_basis_independent :
  bilinear_trace h2 hB hS he = bilinear_trace h2 hB hS hb.
Proof.
rewrite (@bilinear_trace_characterisation R h2 V B S hB hS n e he
  (bilinear_representative hB hS hb) (bilinear_representativeP hB hS hb)).
exact: trace_basis_independent.
Qed.
End Intrinsic.
