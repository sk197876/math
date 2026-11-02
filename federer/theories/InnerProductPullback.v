(** Federer (1969), 1.7.9, p. 35: supporting transfer of the tensor inner
    product through the injective linear identification Gamma. The general
    lemma below is infrastructure, not a separate numbered book assertion. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP BilinearPrecompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_product_linear_pullback]: Federer 1.7.9,
    p. 35, supporting fact: pulling back an inner product along an
    injective linear map gives an inner product. *)
Theorem inner_product_linear_pullback (R : realFieldType)
    (V W : lmodType R) (B : W -> W -> R)
    (hB : is_inner_product B) (f : {linear V -> W}) (hf : injective f) :
  is_inner_product (fun x y => B (f x) (f y)).
Proof.
constructor.
- exact (@bilinear_linear_precompose R V V W W R^o B (inner_bilinear hB) f f).
- move=> x y; exact (inner_symmetric hB (f x) (f y)).
- move=> x; rewrite (inner_positive hB).
  by rewrite -(linear0 f) (inj_eq hf).
Qed.
