(** Federer (1969), 1.7.9, p. 35: supporting evaluation formula for the
    lower comparison between operator norm and tensor norm. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerDual InnerPolarity InnerPolaritySurjection
  TensorInner TensorUP TensorProduct TensorSpan Gamma Hom LinearBasis
  Bilinear OneFormLinear AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [tensor_inner_evaluation]: Federer 1.7.9, p. 35,
    supporting identity: pairing a tensor with the polarity of x
    tensored with y evaluates its associated linear map at x and pairs
    the result with y. This reduces the norm bound to Cauchy's inequality. *)
Theorem tensor_inner_evaluation (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e)
    (t : tensor_space (A_m V R^o 1) W) x y :
  tensor_inner (inner_dual_productP hB he) hC t
    (tensor_inj (inner_polarity hB x) y) = C (@Gamma_inverse R V W t x) y.
Proof.
have hD := inner_bilinear (tensor_inner_productP (inner_dual_productP hB he) hC).
have hE := inner_bilinear hC.
elim/tensor_induction: t.
- by rewrite (bil0l hD) linear0 hom_zeroE (bil0l hE).
- move=> t u ht hu; rewrite (bilDl hD) linearD hom_addE (bilDl hE).
  by rewrite ht hu.
- move=> c t ht; rewrite (bilZl hD) linearZ hom_scaleE (bilZl hE).
  exact (congr1 (fun z : R => c * z) ht).
- move=> a w; have [v <-] := @inner_polarity_surjective R V B hB n e he a.
  by rewrite tensor_innerE inner_dual_polarityE Gamma_inverseE
    one_homE inner_polarityE (bilZl hE) (inner_symmetric hB).
Qed.
