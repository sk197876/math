(** Federer (1969), 4.1.15, p. 372: the original G_r
    behind an opaque seal. Only its independent value law
    is exposed; estimates are theorems proved afterwards. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations RadialAgreementMapUP
  RadialAgreementMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type RadialAgreementMapSignature.
(** Source for [value]: the ambient-valued G_r in
    Federer 4.1.15, p. 372. Arbitrary f,g and
    zero-dimensional source or target are permitted. *)
Parameter value:forall (R:realType) (n nu:nat) (r:R),
  0<r ->(R_n R n->R_n R nu)->(R_n R n->R_n R nu)->
  R_n R n->R_n R nu.
(** Source for [laws]: precisely the original displayed
    value law of G_r in 4.1.15, p. 372. *)
Parameter laws:forall (R:realType) (n nu:nat) (r:R) (hr:0<r)
    (f g:R_n R n->R_n R nu),
  @is_radial_agreement_map R n nu r hr f g (@value R n nu r hr f g).
End RadialAgreementMapSignature.

Module RadialAgreementMap:RadialAgreementMapSignature.
(** Source for [value]: hide the separately proved
    witness of the original definition, 4.1.15, p. 372. *)
Definition value (R:realType) (n nu:nat) (r:R) (hr:0<r)
    (f g:R_n R n->R_n R nu):R_n R n->R_n R nu :=
  projT1 (cid (@radial_agreement_map_exists R n nu r hr f g)).
(** Source for [laws]: the witness satisfies the
    independent G_r law, 4.1.15, p. 372. *)
Lemma laws (R:realType) (n nu:nat) (r:R) (hr:0<r)
    (f g:R_n R n->R_n R nu):
  @is_radial_agreement_map R n nu r hr f g (@value R n nu r hr f g).
Proof.
exact:(projT2 (cid (@radial_agreement_map_exists R n nu r hr f g))).
Qed.
End RadialAgreementMap.
Arguments RadialAgreementMap.value : clear implicits.
Arguments RadialAgreementMap.laws : clear implicits.
