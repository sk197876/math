(** Federer (1969), 1.7.9, p. 35: existence of the characterised tensor
    inner product. This private proof combines the bilinear
    universal-property construction with positivity proved from the
    characterising equation alone. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP TensorUP TensorProduct TensorInnerUP
  TensorInnerBilinearConstruction TensorInnerPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [tensor_inner_exists]: Federer 1.7.9,
    p. 35, existence of the inner product on the tensor product
    of arbitrary-dimensional real inner-product spaces. *)
Theorem tensor_inner_exists (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C) :
  exists D, is_tensor_inner_product B C D.
Proof.
have [D [hD hP]] := tensor_inner_bilinear_exists (inner_bilinear hB) (inner_bilinear hC).
exists D; constructor; last exact hP.
constructor; first exact hD.
- exact (@tensor_form_symmetric R V W B C hB hC D hD hP).
- exact (@tensor_form_positive R V W B C hB hC D hD hP).
Qed.
