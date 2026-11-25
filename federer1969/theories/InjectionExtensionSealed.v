(** Opaque active/complement operators supporting
    Federer (1969), 3.3.4, pp. 289–290.
    Existence was proved from linear algebra;
    downstream users receive only the independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom InjectionExtensionUP InjectionExtensionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type InjectionExtensionSignature.
(** Source for [value]: the uniquely specified
    active/complement operator supporting Federer
    3.3.4, pp. 289–290. *)
Parameter value:forall (K:fieldType) (U V:lmodType K)
  (w:Hom U V) (q:Hom V U) (h:Hom U U),cancel w q ->Hom V V.
(** Source for [laws]: action on the active
    range and identity on its complement,
    supporting Federer 3.3.4, pp. 289–290. *)
Parameter laws:forall (K:fieldType) (U V:lmodType K)
  (w:Hom U V) (q:Hom V U) (h:Hom U U) (hCancel:cancel w q),
  is_injection_extension w q h (@value K U V w q h hCancel).
End InjectionExtensionSignature.
Module InjectionExtension:InjectionExtensionSignature.
(** Source for [value]: private proved existence
    witness for the unique active/complement
    operator supporting Federer 3.3.4, pp. 289–290. *)
Definition value (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (hCancel:cancel w q):=
  projT1 (cid (injection_extension_exists h hCancel)).
(** Source for [laws]: the proved witness obeys
    the independent active/complement laws,
    supporting Federer 3.3.4, pp. 289–290. *)
Lemma laws (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (hCancel:cancel w q):
  is_injection_extension w q h (@value K U V w q h hCancel).
Proof. exact:projT2 (cid (injection_extension_exists h hCancel)). Qed.
End InjectionExtension.
