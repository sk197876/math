(** Federer (1969), 4.1.6, pp. 351–352: the original
    fibre operations act pointwise on fields. All values
    follow from the opaque evaluation and inverse laws;
    no function-space witness is inspected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom TensorUP PointwiseFieldSpaceUP PointwiseFieldSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointwise_field_map]: applying one of
    the original linear or nonlinear fibre operations
    pointwise, Federer 4.1.6, pp. 351–352. *)
Definition pointwise_field_map (K:fieldType) (X:choiceType)
    (Y Z:lmodType K) (L:Y->Z) (f:@PointwiseFieldSpace.space K X Y):
    @PointwiseFieldSpace.space K X Z:=
  @PointwiseFieldSpace.of_function K X Z (fun x=>L (@PointwiseFieldSpace.value K X Y f x)).

(** Source for [pointwise_field_map_values]: exact
    pointwise evaluation, Federer 4.1.6, pp. 351–352. *)
Lemma pointwise_field_map_values (K:fieldType) (X:choiceType)
    (Y Z:lmodType K) (L:Y->Z) (f:@PointwiseFieldSpace.space K X Y) x:
  @PointwiseFieldSpace.value K X Z (pointwise_field_map L f) x=
    L (@PointwiseFieldSpace.value K X Y f x).
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.

(** Source for [pointwise_field_map_linear]: linear
    fibre operations induce linear field operations,
    Federer 4.1.6, pp. 351–352. *)
Lemma pointwise_field_map_linear (K:fieldType) (X:choiceType)
    (Y Z:lmodType K) (L:Hom Y Z):linear (@pointwise_field_map K X Y Z L).
Proof.
move=>c f g; apply:(pointwise_field_extensional (@PointwiseFieldSpace.laws K X Z))=>x.
rewrite pointwise_field_map_values !pointwise_field_linear_values pointwise_field_map_values.
rewrite pointwise_field_map_values; exact:linearP.
Qed.

(** Source for [pointwise_field_binary]: the original
    alternating products, contractions, pairings and
    inner products act pointwise, Federer 4.1.6,
    pp. 351–352. *)
Definition pointwise_field_binary (K:fieldType) (X:choiceType)
    (Y Z T:lmodType K) (B:Y->Z->T)
    (f:@PointwiseFieldSpace.space K X Y) (g:@PointwiseFieldSpace.space K X Z):
    @PointwiseFieldSpace.space K X T:=
  @PointwiseFieldSpace.of_function K X T
    (fun x=>B (@PointwiseFieldSpace.value K X Y f x) (@PointwiseFieldSpace.value K X Z g x)).

(** Source for [pointwise_field_binary_values]: the
    exact value of each pointwise fibre product,
    Federer 4.1.6, pp. 351–352. *)
Lemma pointwise_field_binary_values (K:fieldType) (X:choiceType)
    (Y Z T:lmodType K) (B:Y->Z->T)
    (f:@PointwiseFieldSpace.space K X Y) (g:@PointwiseFieldSpace.space K X Z) x:
  @PointwiseFieldSpace.value K X T (pointwise_field_binary B f g) x=
    B (@PointwiseFieldSpace.value K X Y f x) (@PointwiseFieldSpace.value K X Z g x).
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.

(** Source for [pointwise_field_binary_bilinear]: the
    pointwise products retain the original bilinearity,
    Federer 4.1.6, pp. 351–352. *)
Lemma pointwise_field_binary_bilinear (K:fieldType) (X:choiceType)
    (Y Z T:lmodType K) (B:Y->Z->T):
  bilinear B ->bilinear (@pointwise_field_binary K X Y Z T B).
Proof.
move=>hB; split.
- move=>g c f f'; apply:(pointwise_field_extensional (@PointwiseFieldSpace.laws K X T))=>x.
  rewrite pointwise_field_binary_values !pointwise_field_linear_values !pointwise_field_binary_values.
  exact:hB.1.
- move=>f c g g'; apply:(pointwise_field_extensional (@PointwiseFieldSpace.laws K X T))=>x.
  rewrite pointwise_field_binary_values !pointwise_field_linear_values !pointwise_field_binary_values.
  exact:hB.2.
Qed.
