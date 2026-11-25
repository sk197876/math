(** Federer (1969), 1.7.13, p. 37: the residual from a nearest point in a
    vector subspace is orthogonal to that subspace. The proof evaluates the
    printed quadratic at its minimising scalar, using the local
    completed-square identity. Completeness is needed only for existence of
    the nearest point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import ModuleQuotient InnerProductUP InnerProductLaws
  InnerCauchy InnerNorm InnerNearestUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_subspace_convex]: Federer 1.7.13,
    p. 37, supporting applicability of the convex nearest-point
    theorem to a vector subspace: every affine segment stays in it. *)
Lemma inner_subspace_convex (R : realFieldType) (V : lmodType R)
    (S : subspace V) x y (hx : S x) (hy : S y) (t : R) :
    S ((1-t)*:x+t*:y).
Proof. exact: subspace_add (subspace_scale _ hx) (subspace_scale _ hy). Qed.

(** Source for [inner_nearest_subspace_orthogonal]: Federer
    1.7.13, p. 37, the displayed equation (a-c).x=0 for x
    in the subspace. It holds for any point satisfying the nearest
    point specification, independently of how that point is obtained. *)
Theorem inner_nearest_subspace_orthogonal (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (S : subspace V) a c (hc : is_inner_nearest hB a S c) x :
    S x -> B (a-c) x = 0.
Proof.
move=> hx; have [->|hx0] := eqVneq x 0; first by rewrite (bil0r (inner_bilinear hB)).
have hcx := subspace_add (inner_nearest_member_law hc)
  (subspace_scale (B (a-c) x / B x x) hx).
have hm := inner_nearest_minimal_law hc hcx.
have he : a-(c+(B (a-c) x / B x x)*:x) = (a-c)-(B (a-c) x / B x x)*:x.
  by rewrite opprD addrA.
have hm2 : inner_norm hB (a-c)^+2 <=
    inner_norm hB ((a-c)-(B (a-c) x / B x x)*:x)^+2.
  rewrite (ler_sqr (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _)).
  by rewrite -he.
rewrite !inner_norm_sqr (inner_residual_square hB (a-c) hx0) lerDl oppr_ge0 in hm2.
have hp : 0 < B x x by rewrite (inner_positive hB).
have hq : 0 <= B (a-c) x ^+2 / B x x by exact: divr_ge0 (sqr_ge0 _) (ltW hp).
have hz : B (a-c) x ^+2 / B x x = 0 by apply/eqP; rewrite eq_le hm2 hq.
move/eqP: hz; rewrite mulf_eq0 invr_eq0 (negbTE (lt0r_neq0 hp)) orbF sqrf_eq0.
exact/eqP.
Qed.
