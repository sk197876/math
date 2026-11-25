(** Federer (1969), 4.1.6, p. 354: opaque
    original pullback, retaining its actual derivative
    and target domains. Its exact graph was specified
    independently and proved to exist. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import RealNormUP AlternatingForms PartialFunctionUP
  DifferentialFormPullbackUP DifferentialFormPullbackConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type DifferentialFormPullbackSignature.
(** Source for [value]: the original f# phi,
    Federer 4.1.6, p. 354. *)
Parameter value:forall (R:realType) (X Y W:lmodType R)
  (NX:X->R) (NY:Y->R),is_real_norm NX->is_real_norm NY->
  (X->Prop)->(Y->Prop)->(X->Y)->forall m,(Y->A_m Y W m)->partial_function X (A_m X W m).
(** Source for [laws]: the exact original graph,
    Federer 4.1.6, p. 354. *)
Parameter laws:forall (R:realType) (X Y W:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi:Y->A_m Y W m),
  is_differential_form_pullback_graph NX NY A B f phi
    (@value R X Y W NX NY hNX hNY A B f m phi).
End DifferentialFormPullbackSignature.
Module DifferentialFormPullback:DifferentialFormPullbackSignature.
(** Source for [value]: select the proved pullback,
    Federer 4.1.6, p. 354. *)
Definition value (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi:Y->A_m Y W m):partial_function X (A_m X W m):=
  projT1 (cid (@differential_form_pullback_exists R X Y W NX NY hNX hNY A B f m phi)).
(** Source for [laws]: the selected pullback has every
    original graph pair, Federer 4.1.6, p. 354. *)
Lemma laws (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi:Y->A_m Y W m):
  is_differential_form_pullback_graph NX NY A B f phi
    (@value R X Y W NX NY hNX hNY A B f m phi).
Proof. exact:projT2 (cid (@differential_form_pullback_exists R X Y W NX NY hNX hNY A B f m phi)). Qed.
End DifferentialFormPullback.
