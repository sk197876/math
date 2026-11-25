(** Federer (1969), 4.1.7, p. 357: existence
    of the original multivector-to-dual evaluation map,
    from the bilinear pairing of 1.4.1, p. 17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Bilinear Hom ExteriorGrading AlternatingForms AlternatingPairing
  PairingLinear MultivectorDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section MultivectorDualExistence.
Variable K:fieldType.
Variable V:lmodType K.
Variable m:nat.

(** Source for [multivector_pairing_functional]: the
    original evaluation at a multivector is linear
    on covectors, supporting Federer 4.1.7, p. 357. *)
Definition multivector_pairing_functional (xi:exterior_power V m):Hom (A_m V K^o m) K^o:=
  hom_of_linear (pairing_right xi).

(** Source for [multivector_pairing_functional_linear]:
    evaluation is linear in the multivector too,
    supporting Federer 4.1.7, p. 357. *)
Lemma multivector_pairing_functional_linear:linear multivector_pairing_functional.
Proof.
move=>c xi eta; apply:hom_ext=>phi.
change (pairing (c*:xi+eta) phi=c*:pairing xi phi+pairing eta phi).
by rewrite (bilDl (@pairing_bilinear K V K^o m))
  (bilZl (@pairing_bilinear K V K^o m)).
Qed.

(** Source for [multivector_dual_pairing_exists]: the
    independently specified original pairing map
    exists, supporting Federer 4.1.7, p. 357. *)
Theorem multivector_dual_pairing_exists:
  exists E:Hom (exterior_power V m) (Hom (A_m V K^o m) K^o),
    is_multivector_dual_pairing E.
Proof.
exists (@HomMap K (exterior_power V m) (Hom (A_m V K^o m) K^o)
  multivector_pairing_functional (introT (asboolP _) multivector_pairing_functional_linear)).
by move=>xi phi.
Qed.
End MultivectorDualExistence.
