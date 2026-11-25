(** Federer (1969), 4.1.7, p. 357: identify
    multivectors with the real dual of covectors by
    the original pairing. This specification precedes
    the existence and norm proofs. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom ExteriorGrading AlternatingForms AlternatingPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_multivector_dual_pairing]: the original
    identification Y*=Lambda_m R^n in Federer 4.1.7,
    p. 357, specified by evaluation. *)
Definition is_multivector_dual_pairing (K:fieldType) (V:lmodType K) m
    (E:Hom (exterior_power V m) (Hom (A_m V K^o m) K^o)):=
  forall xi phi,E xi phi=pairing xi phi.

(** Source for [multivector_dual_pairing_unique]: the
    original evaluation determines the identification,
    supporting Federer 4.1.7, p. 357. *)
Lemma multivector_dual_pairing_unique (K:fieldType) (V:lmodType K) m
    (E F:Hom (exterior_power V m) (Hom (A_m V K^o m) K^o)):
  is_multivector_dual_pairing E ->is_multivector_dual_pairing F ->E=F.
Proof.
move=>hE hF; apply:hom_ext=>xi; apply:hom_ext=>phi.
by rewrite (hE xi phi) (hF xi phi).
Qed.
