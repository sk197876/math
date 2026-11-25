(** Federer (1969), 4.1.7, p. 357: opaque
    original evaluation identification of multivectors
    with covector functionals. Its existence witness
    stays behind the public pairing law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ExteriorGrading AlternatingForms
  MultivectorDualUP MultivectorDualExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type MultivectorDualSignature.
(** Source for [evaluation]: the original canonical
    map into the covector dual, Federer 4.1.7, p. 357. *)
Parameter evaluation:forall (K:fieldType) (V:lmodType K) m,
  Hom (exterior_power V m) (Hom (A_m V K^o m) K^o).
(** Source for [laws]: exact original pairing values,
    Federer 4.1.7, p. 357. *)
Parameter laws:forall (K:fieldType) (V:lmodType K) m,
  is_multivector_dual_pairing (@evaluation K V m).
End MultivectorDualSignature.
Module MultivectorDual:MultivectorDualSignature.
(** Source for [evaluation]: hide the proved canonical
    map witness, supporting Federer 4.1.7, p. 357. *)
Definition evaluation (K:fieldType) (V:lmodType K) m:
    Hom (exterior_power V m) (Hom (A_m V K^o m) K^o):=
  projT1 (cid (@multivector_dual_pairing_exists K V m)).
(** Source for [laws]: the opaque map satisfies its
    independent original specification, supporting
    Federer 4.1.7, p. 357. *)
Lemma laws (K:fieldType) (V:lmodType K) m:
  is_multivector_dual_pairing (@evaluation K V m).
Proof. exact:(projT2 (cid (@multivector_dual_pairing_exists K V m))). Qed.
End MultivectorDual.
