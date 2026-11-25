(** Federer (1969), 1.7.9, p. 35: the tensor inner product is characterised
    by (v tensor w) dot (v' tensor w') = (v dot v')(w dot w'). Neither
    factor is required to be finite-dimensional. The defining laws precede
    existence; a private construction will be sealed behind this
    specification. Erratum p. 1, book p. 35 line 3, restores the prime on w'
    in the tensor-product inner-product formula (v (x) w) . (v' (x) w'). *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP TensorProduct TensorSpan Bilinear AlgebraTensor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_tensor_inner_product]: Federer 1.7.9,
    p. 35, defining equation together with the assertion that
    it gives an inner product. This record specifies laws only. *)
Record is_tensor_inner_product (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (D : tensor_space V W -> tensor_space V W -> R) : Prop := {
  tensor_inner_laws : is_inner_product D;
  tensor_inner_pure : forall v w v' w',
    D (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w'
}.

(** Source for [tensor_inner_unique]: Federer 1.7.9,
    p. 35, the characterising equation determines the inner product
    uniquely. This uses only the abstract specification. *)
Theorem tensor_inner_unique (R : realFieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (D F : tensor_space V W -> tensor_space V W -> R) :
  is_tensor_inner_product B C D -> is_tensor_inner_product B C F ->
  forall x y, D x y = F x y.
Proof.
move=> hD hF; apply: tensor_bilinear_ext
  (inner_bilinear (tensor_inner_laws hD)) (inner_bilinear (tensor_inner_laws hF)) _.
by move=> v w v' w'; rewrite (tensor_inner_pure hD) (tensor_inner_pure hF).
Qed.
