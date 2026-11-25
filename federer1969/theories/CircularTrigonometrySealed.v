(** Opaque circular trigonometry for Federer (1969),
    3.3.19, p. 302. Only independently proved scalar
    laws cross the seal; all geometry is proved downstream. *)
From mathcomp Require Import all_boot boolp reals.
From Federer Require Import CircularTrigonometryUP CircularTrigonometryConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CircularTrigonometrySignature.
(** Source for [sine]: elementary circular scalar
    background for 3.3.19, p. 302, exposed abstractly. *)
Parameter sine:forall R:realType,R->R.
(** Source for [cosine]: elementary circular scalar
    background for 3.3.19, p. 302, exposed abstractly. *)
Parameter cosine:forall R:realType,R->R.
(** Source for [arcsine]: elementary circular scalar
    background for 3.3.19, p. 302, exposed abstractly. *)
Parameter arcsine:forall R:realType,R->R.
(** Source for [arccosine]: elementary circular scalar
    background for 3.3.19, p. 302, exposed abstractly. *)
Parameter arccosine:forall R:realType,R->R.
(** Source for [half_period]: elementary circular scalar
    background for 3.3.19, p. 302, exposed abstractly. *)
Parameter half_period:forall R:realType,R.
(** Source for [laws]: proved elementary circular laws
    supporting the centres of 3.3.19, p. 302. *)
Parameter laws:forall R:realType,is_circular_trigonometry (@sine R) (@cosine R) (@arcsine R) (@arccosine R) (@half_period R).
End CircularTrigonometrySignature.
Module CircularTrigonometry:CircularTrigonometrySignature.
(** Source for [sine]: hidden local existence witness
    for the circular centres of 3.3.19, p. 302. *)
Definition sine (R:realType):=projT1 (cid (circular_trigonometry_exists R)).
(** Source for [cosine]: hidden local existence witness
    for the circular centres of 3.3.19, p. 302. *)
Definition cosine (R:realType):=projT1 (cid (projT2 (cid (circular_trigonometry_exists R)))).
(** Source for [arcsine]: hidden local existence witness
    for the circular centres of 3.3.19, p. 302. *)
Definition arcsine (R:realType):=projT1 (cid (projT2 (cid (projT2 (cid (circular_trigonometry_exists R)))))).
(** Source for [arccosine]: hidden local existence witness
    for the circular centres of 3.3.19, p. 302. *)
Definition arccosine (R:realType):=projT1 (cid (projT2 (cid (projT2 (cid (projT2 (cid (circular_trigonometry_exists R)))))))).
(** Source for [half_period]: hidden local existence witness
    for the circular centres of 3.3.19, p. 302. *)
Definition half_period (R:realType):=projT1 (cid (projT2 (cid (projT2 (cid (projT2 (cid (projT2 (cid (circular_trigonometry_exists R)))))))))).
(** Source for [laws]: the selected witnesses satisfy
    the scalar specification for 3.3.19, p. 302. *)
Lemma laws (R:realType):is_circular_trigonometry (@sine R) (@cosine R) (@arcsine R) (@arccosine R) (@half_period R).
Proof. exact:(projT2 (cid (projT2 (cid (projT2 (cid (projT2 (cid (projT2 (cid (circular_trigonometry_exists R))))))))))). Qed.
End CircularTrigonometry.
