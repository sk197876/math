(** Federer (1969), 1.7.13, p. 37: nearest points
    of a closed convex set. This supporting consequence
    of the minimizing laws is used to extend local
    coordinate maps without leaving their target chart in
    the localization of 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities
  InnerConvex InnerNearestUP NearestConvexVariational Bilinear BilinearNegation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_nearest_pair_nonexpanding]: actual
    nearest points c,d to x,y in the same convex set
    satisfy |c-d|<=|x-y|, supporting the nearest-point
    procedure of 1.7.13, p. 37, and local chart
    extensions in 3.2.46, p. 282. Only the proved
    minimizing laws are used; no projection construction
    or extra contraction law is assumed. *)
Lemma inner_nearest_pair_nonexpanding (R : realType) (V : lmodType R) B
    (hB : @is_inner_product R V B) (C : V -> Prop) x y c d :
  is_inner_convex C -> is_inner_nearest hB x C c -> is_inner_nearest hB y C d ->
  inner_norm hB (c-d)<=inner_norm hB (x-y).
Proof.
move=> hC hc hd.
have hFirst := @inner_nearest_convex_variational R V B hB C hC x c hc d
  (inner_nearest_member_law hd).
have hSecond := @inner_nearest_convex_variational R V B hB C hC y d hd c
  (inner_nearest_member_law hc).
rewrite -[d-c]opprB (bilNr (inner_bilinear hB)) oppr_le0 in hFirst.
have hAlgebra : B (x-y) (c-d)=B (c-d) (c-d)+B (x-c) (c-d)-B (y-d) (c-d).
  rewrite !(bilBl (inner_bilinear hB)); ring.
have hLower : (inner_norm hB (c-d))^+2<=B (x-y) (c-d).
  rewrite inner_norm_sqr hAlgebra; lra.
have hUpper : B (x-y) (c-d)<=inner_norm hB (x-y)*inner_norm hB (c-d).
  exact: le_trans (ler_norm _) (inner_cauchy hB (x-y) (c-d)).
have hProduct := le_trans hLower hUpper.
case: (eqVneq (inner_norm hB (c-d)) 0)=> [->|hNe]; first exact: inner_norm_nonnegative.
have hPositive : 0<inner_norm hB (c-d) by rewrite lt_def hNe inner_norm_nonnegative.
rewrite expr2 (ler_pM2r hPositive) in hProduct; exact hProduct.
Qed.
