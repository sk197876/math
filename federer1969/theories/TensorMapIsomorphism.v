(** Federer (1969), 1.7.9, p. 35: the tensor product of two automorphisms is
    an automorphism. Supporting functorial inverse laws, already implicit in
    1.1.2, p. 10. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorMaps LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [tensor_map_cancel]: Federer 1.7.9, p. 35,
    supporting inverse law: tensor products preserve two inverse
    maps. It follows from their action on pure tensors. *)
Theorem tensor_map_cancel (R : fieldType) (V W V' W' : lmodType R)
    (f : {linear V -> V'}) (g : {linear W -> W'})
    (a : {linear V' -> V}) (b : {linear W' -> W}) :
  cancel f a -> cancel g b -> cancel (tensor_map f g) (tensor_map a b).
Proof.
move=> hf hg.
apply: (tensor_ext (tensor_exists V W)
  (linear_comp (tensor_map a b) (tensor_map f g)) (linear_id _)).
by move=> v w /=; rewrite !tensor_mapE hf hg.
Qed.

(** Source for [tensor_map_bijective]: Federer 1.7.9, p. 35,
    supporting automorphism assertion: the tensor map of two
    bijective linear maps is bijective, in arbitrary dimension. *)
Theorem tensor_map_bijective (R : fieldType) (V W V' W' : lmodType R)
    (f : {linear V -> V'}) (g : {linear W -> W'}) :
  bijective f -> bijective g -> bijective (tensor_map f g).
Proof.
move=> [a ha ha'] [b hb hb'].
have hs : forall y, exists x, f x = y by move=> y; exists (a y).
have ht : forall y, exists x, g x = y by move=> y; exists (b y).
pose ai := GRing.Linear.clone _ _ _ _ (linear_inverse (can_inj ha) hs) _.
pose bi := GRing.Linear.clone _ _ _ _ (linear_inverse (can_inj hb) ht) _.
exists (tensor_map ai bi).
- apply: tensor_map_cancel; exact: linear_inverseKV.
- apply: tensor_map_cancel; exact: linear_inverseK.
Qed.
