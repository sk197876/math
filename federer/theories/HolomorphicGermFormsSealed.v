(** Federer (1969), 3.4.12, pp. 338–339:
    the actual original complex derivative forms are opaque.
    Their public interface contains only the independently
    specified actual jet equation, after existence is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  SymmetricForms HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicGermFormsSignature.
(** Source for [value]: original complex differential
    form of a germ, 3.4.12, pp. 338–339. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) (a:X) k,
  holomorphic_germ_space (complex_norm_real hNX) a->S_m X (ComplexScalars.C R)^o k.
(** Source for [laws]: actual original tuple evaluation
    equals the actual jet, 3.4.12, pp. 338–339. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:is_complex_norm NX) (a:X) k alpha,
  @is_holomorphic_germ_form R X NX hNX a k alpha (@value R X NX hNX a k alpha).
End HolomorphicGermFormsSignature.
Module HolomorphicGermForms:HolomorphicGermFormsSignature.
(** Source for [value]: select the proved original
    complex form witness, 3.4.12, pp. 338–339. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (a:X) k alpha:=
  projT1 (cid (@holomorphic_germ_form_exists R X NX hNX a k alpha)).
(** Source for [laws]: the selected form satisfies
    its independent actual jet equation, 3.4.12,
    pp. 338–339. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (a:X) k alpha:
  @is_holomorphic_germ_form R X NX hNX a k alpha (@value R X NX hNX a k alpha).
Proof. exact:(projT2 (cid (@holomorphic_germ_form_exists R X NX hNX a k alpha))). Qed.
End HolomorphicGermForms.
