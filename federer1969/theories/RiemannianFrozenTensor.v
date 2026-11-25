(** Federer (1969), 3.2.46, p. 281: freeze the continuous
    tensor at a single original point when comparing the curve
    integrals. The constant field is a proved local example of
    the independent tensor laws, with no selected frame field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm NormDifferentialUP RiemannianTensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_frozen_tensor_laws]: a fixed
    positive inner product gives a continuous tensor on the
    original open domain, supporting the frozen comparison in
    Federer 3.2.46, p. 281. All dimensions are included. *)
Lemma riemannian_frozen_tensor_laws (R : realType) n A B
    (hB : @is_inner_product R (R_n R n) B) :
  (forall a, A a -> norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A a) ->
  @is_continuous_riemannian_tensor R n A (fun _=>B).
Proof.
move=> hOpen; constructor.
- by move=> x hx.
- exact: hOpen.
- move=> a ha e he; exists 1; split; first exact: ltr01.
  move=> h hh hSmall u v; rewrite subrr normr0.
  exact: mulr_ge0 (mulr_ge0 (ltW he) (inner_norm_nonnegative _ _))
    (inner_norm_nonnegative _ _).
Qed.
