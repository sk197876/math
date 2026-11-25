(** Federer (1969), 4.1.6, p. 351: opaque pointwise
    field spaces. The original function model is hidden;
    consumers use evaluation, linearity and fullness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom PointwiseFieldSpaceUP PointwiseFieldSpaceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PointwiseFieldSpaceSignature.
(** Source for [space]: the vector space of all original
    fibre-valued maps, Federer 4.1.6, p. 351. *)
Parameter space:forall (K:fieldType) (X:choiceType) (Y:lmodType K),lmodType K.
(** Source for [value]: the actual pointwise values of a
    field or differential form, Federer 4.1.6, p. 351. *)
Parameter value:forall (K:fieldType) (X:choiceType) (Y:lmodType K),
  Hom (@space K X Y) (GRing.Lmodule.clone K (X->Y) _).
(** Source for [laws]: exact evaluation and representation
    laws of the original fields, Federer 4.1.6, p. 351. *)
Parameter laws:forall (K:fieldType) (X:choiceType) (Y:lmodType K),
  is_pointwise_field_space (@value K X Y).
(** Source for [of_function]: the inverse of original pointwise
    evaluation, Federer 4.1.6, p. 351. *)
Parameter of_function:forall (K:fieldType) (X:choiceType) (Y:lmodType K),
  (X->Y)->@space K X Y.
(** Source for [value_of_function]: representing a function
    preserves its original values, Federer 4.1.6, p. 351. *)
Parameter value_of_function:forall (K:fieldType) (X:choiceType) (Y:lmodType K)
  (f:X->Y) x,@value K X Y (@of_function K X Y f) x=f x.
(** Source for [of_function_value]: a field is uniquely
    determined by its original values, Federer 4.1.6, p. 351. *)
Parameter of_function_value:forall (K:fieldType) (X:choiceType) (Y:lmodType K)
  (f:@space K X Y),@of_function K X Y (@value K X Y f)=f.
End PointwiseFieldSpaceSignature.
Module PointwiseFieldSpace:PointwiseFieldSpaceSignature.
(** Source for [space]: hide the proved function-space
    witness, Federer 4.1.6, p. 351. *)
Definition space (K:fieldType) (X:choiceType) (Y:lmodType K):lmodType K:=
  projT1 (cid (@pointwise_field_space_exists K X Y)).
(** Source for [value]: hidden witness evaluation,
    Federer 4.1.6, p. 351. *)
Definition value (K:fieldType) (X:choiceType) (Y:lmodType K):
    Hom (@space K X Y) (GRing.Lmodule.clone K (X->Y) _):=
  projT1 (cid (projT2 (cid (@pointwise_field_space_exists K X Y)))).
(** Source for [laws]: the hidden witness has the
    independent original laws, Federer 4.1.6, p. 351. *)
Lemma laws (K:fieldType) (X:choiceType) (Y:lmodType K):
  is_pointwise_field_space (@value K X Y).
Proof. exact:(projT2 (cid (projT2 (cid (@pointwise_field_space_exists K X Y))))). Qed.
(** Source for [of_function]: select the already proved
    field representative behind the opaque interface,
    Federer 4.1.6, p. 351. *)
Definition of_function (K:fieldType) (X:choiceType) (Y:lmodType K)
    (f:X->Y):@space K X Y:=
  proj1_sig (cid (pointwise_field_represents (@laws K X Y) f)).
(** Source for [value_of_function]: the selected representative
    has the independent evaluation laws, Federer 4.1.6,
    p. 351. *)
Lemma value_of_function (K:fieldType) (X:choiceType) (Y:lmodType K)
    (f:X->Y) x:@value K X Y (@of_function K X Y f) x=f x.
Proof. exact:(proj2_sig (cid (pointwise_field_represents (@laws K X Y) f))). Qed.
(** Source for [of_function_value]: extensionality proves
    the inverse law, Federer 4.1.6, p. 351. *)
Lemma of_function_value (K:fieldType) (X:choiceType) (Y:lmodType K)
    (f:@space K X Y):@of_function K X Y (@value K X Y f)=f.
Proof.
apply:(pointwise_field_extensional (@laws K X Y))=>x.
exact:value_of_function.
Qed.
End PointwiseFieldSpace.
