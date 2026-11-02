(** Opaque locally finite sum for Federer (1969),
    3.1.13, p. 225. Only its
    evaluation on finite active selections is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp.
From Federer Require Import FiniteFamilySumUP FiniteFamilySumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type FiniteFamilySumSignature.
(** Source for [value]: the sum of the
    locally finite family, Federer 3.1.13,
    p. 225, on its specified domain. *)
Parameter value : forall (X : Type) (J : choiceType) (Y : zmodType)
  (U : X->Prop) (I : J->Prop) (f : J->X->Y),
  finite_active_family_on U I f -> X->Y.
(** Source for [laws]: the finite evaluation
    laws of the sum in Federer 3.1.13,
    p. 225, are proved by the implementation. *)
Parameter laws : forall (X : Type) (J : choiceType) (Y : zmodType)
  (U : X->Prop) (I : J->Prop) (f : J->X->Y)
  (hfin : finite_active_family_on U I f),
  is_finite_family_sum_on U I f (@value X J Y U I f hfin).
End FiniteFamilySumSignature.

Module FiniteFamilySum : FiniteFamilySumSignature.
(** Source for [value]: the privately proved
    sum witness, Federer 3.1.13, p. 225. *)
Definition value (X : Type) (J : choiceType) (Y : zmodType)
    (U : X->Prop) (I : J->Prop) (f : J->X->Y)
    (hfin : finite_active_family_on U I f) : X->Y :=
  projT1 (cid (@finite_family_sum_exists X J Y U I f hfin)).
(** Source for [laws]: proof of the
    public sum specification, Federer 3.1.13, p. 225. *)
Lemma laws (X : Type) (J : choiceType) (Y : zmodType)
    (U : X->Prop) (I : J->Prop) (f : J->X->Y)
    (hfin : finite_active_family_on U I f) :
  is_finite_family_sum_on U I f (@value X J Y U I f hfin).
Proof. exact: projT2 (cid (@finite_family_sum_exists X J Y U I f hfin)). Qed.
End FiniteFamilySum.
