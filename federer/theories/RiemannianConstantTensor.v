(** Federer (1969), 3.2.46, p. 281: constant positive inner products
    are continuous Riemannian tensors. This supporting witness permits
    concrete regressions of the actual metric and transformation laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerProductLaws RiemannianTensorUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_constant_tensor]: constant-field instance
    of the continuous positive tensor in Federer 3.2.46, p. 281.
    The inner product may be any positive form, rather than the usual
    coordinate form; the original domain is the whole Euclidean space. *)
Lemma riemannian_constant_tensor (R:realType) n
    (B:R_n R n->R_n R n->R) (hB:is_inner_product B):
  @is_continuous_riemannian_tensor R n setT (fun _=>B).
Proof.
constructor.
- by move=>x _.
- move=>x _; exists 1; split; first exact:ltr01.
  by move=>v _.
- move=>x _ e he; exists 1; split; first exact:ltr01.
  move=>v _ _ u w; rewrite subrr normr0.
  apply:mulr_ge0; last exact:inner_norm_nonnegative.
  exact:mulr_ge0 (ltW he) (inner_norm_nonnegative _ _).
Qed.
