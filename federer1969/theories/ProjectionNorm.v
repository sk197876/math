(** Federer (1969), 1.7.7, p. 34: orthogonal projections and their
    top-target exterior maps do not increase length. Neither passage states
    Federer's projection supremum formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  OrthogonalMaps AdjointUP AdjointCriteria OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_projection_norm_bound]: Federer
    1.7.7, p. 34, supporting contraction property of an
    orthogonal projection. It holds also when its target is zero. *)
Theorem orthogonal_projection_norm_bound (R : rcfType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (hp : is_orthogonal_projection B C p) x :
  inner_norm hC (p x) <= inner_norm hB x.
Proof.
have [a [ho ha]] := hp.
have [hz|hz] := eqVneq (p x) 0.
- rewrite hz inner_norm0; exact: inner_norm_nonnegative.
have hn : 0 < inner_norm hC (p x) by rewrite inner_norm_gt0.
have hc := le_trans (ler_norm (B (a (p x)) x)) (inner_cauchy hB (a (p x)) x).
rewrite -ha -inner_norm_sqr
  (@orthogonal_map_norm R U V C B hC hB a ho) expr2 in hc.
by move: hc; rewrite (ler_pM2l hn).
Qed.

(** Source for [orthogonal_projection_unit_norm]: Federer
    1.7.7, p. 34, the norm of an orthogonal projection is one
    if its target has a unit vector. This hypothesis records the
    necessary exception for a zero-dimensional target. *)
Theorem orthogonal_projection_unit_norm (R : rcfType)
    (V U : lmodType R) (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (p : {linear V -> U}) (hp : is_orthogonal_projection B C p)
    u (hu : inner_norm hC u = 1) : is_operator_norm hB hC p 1.
Proof.
constructor.
- move=> x hx; exact: le_trans (orthogonal_projection_norm_bound hB hC hp x) hx.
- have [a [ho ha]] := hp.
  have hk := proj1 (@orthogonal_iff_adjoint_left_inverse R U V C B hC a p ha) ho.
  exists (a u); split.
  + by rewrite (@orthogonal_map_norm R U V C B hC hB a ho) hu.
  + by rewrite hk hu.
Qed.
