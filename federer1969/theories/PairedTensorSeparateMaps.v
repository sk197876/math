(** Federer (1969), 4.1.8, p. 360: the two
    independent factor projections in the separated product
    pairing. This supporting naturality law uses the original
    binary tensor universal property and the coefficient
    pairing of 1.4.2, p. 18. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom Tensor TensorUP TensorMaps Convolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PairedTensorSeparateMaps.
Variable K:fieldType.
Variables X Y U V W:lmodType K.
Variables (f:{linear X->U}) (g:{linear Y->V}).
Variable mu:W->W->W.
Hypothesis hmu:bilinear mu.

(** Source for [paired_tensor_separate_maps]: precomposing
    the two factor functionals agrees with applying the two
    factor maps to their tensor, supporting Federer 4.1.8,
    p. 360. This extends the existing same-map
    naturality law only to distinct factor maps. *)
Theorem paired_tensor_separate_maps (a:Hom U W) (b:Hom V W) x:
  paired_tensor hmu a b (tensor_map f g x)=
    paired_tensor hmu (hom_comp a (hom_of_linear f))
      (hom_comp b (hom_of_linear g)) x.
Proof.
apply:(tensor_ext (tensor_exists X Y)
  (linear_comp (paired_tensor hmu a b) (tensor_map f g))
  (paired_tensor hmu (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear g)))) x=>u v.
change (paired_tensor hmu a b (tensor_map f g (tensor_inj u v))=
  paired_tensor hmu (hom_comp a (hom_of_linear f)) (hom_comp b (hom_of_linear g))
    (tensor_inj u v)).
by rewrite tensor_mapE !paired_tensorE !hom_compE !hom_of_linearE.
Qed.
End PairedTensorSeparateMaps.
