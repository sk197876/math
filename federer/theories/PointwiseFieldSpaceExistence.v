(** Federer (1969), 4.1.6, p. 351: existence of the
    pointwise vector space of all forms or multivector
    fields. The literal function model is an existence
    witness for the independent evaluation specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import TensorUP Hom PointwiseFieldSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointwise_field_space_exists]: the pointwise
    vector space in Federer 4.1.6, p. 351,
    exists for every domain and coefficient fibre. This
    includes empty domains and zero fibres. *)
Theorem pointwise_field_space_exists (K:fieldType) (X:choiceType) (Y:lmodType K):
  exists (E:lmodType K) (ev:Hom E (GRing.Lmodule.clone K (X->Y) _)),
    is_pointwise_field_space ev.
Proof.
pose E:=GRing.Lmodule.clone K (X->Y) _.
pose ev:Hom E E:=hom_of_linear (linear_id E).
exists E,ev; constructor.
- move=>f g h; exact:funext h.
- move=>f; by exists f.
Qed.
