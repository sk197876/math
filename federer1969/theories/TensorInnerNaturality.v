(** Federer (1969), 1.7.9, p. 35: the tensor map of orthogonal maps is
    orthogonal, as used for the change of orthogonal coordinates on
    Hom(V,W). No finite dimension is required. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthogonalMaps TensorUP TensorProduct TensorMaps
  TensorInner TensorInnerUP AlgebraTensor BilinearPrecompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [tensor_map_orthogonal]: Federer 1.7.9,
    p. 35, the tensor product of orthogonal injections preserves
    the induced inner product. Automorphism consequences follow
    by applying the tensor functor to their inverses. *)
Theorem tensor_map_orthogonal (R : rcfType) (V W V' W' : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (B' : V' -> V' -> R) (C' : W' -> W' -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (hB' : is_inner_product B') (hC' : is_inner_product C')
    (f : {linear V -> V'}) (g : {linear W -> W'})
    (hf : is_orthogonal_map B B' f) (hg : is_orthogonal_map C C' g) :
  is_orthogonal_map (tensor_inner hB hC) (tensor_inner hB' hC') (tensor_map f g).
Proof.
apply: tensor_bilinear_ext
  (bilinear_linear_precompose (inner_bilinear (tensor_inner_productP hB' hC'))
    (tensor_map f g) (tensor_map f g))
  (inner_bilinear (tensor_inner_productP hB hC)) _ => v w v' w'.
by rewrite !tensor_mapE !tensor_innerE hf hg.
Qed.
