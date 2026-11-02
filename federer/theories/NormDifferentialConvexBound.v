(** Federer (1969), 3.1.1, pp. 210–211: derivative bounds imply
    increment bounds on convex sets, by the cited criterion 2.2.7, p. 64. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric InnerConvex
  NormDifferentialUP ConvexLocalLipschitz LocalSlopeBound LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_convex_bound]: the application of
    Federer 2.2.7, p. 64, in the inverse-function proof of 3.1.1, p. 210.
    A common bound M for differentials at all points of a convex subset
    implies the same Lipschitz bound there. The surrounding differentiable
    domain may be larger; no completeness or finite dimension is required. *)
Theorem norm_differential_convex_bound (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A U : set X) (f : X -> Y) (M : R) :
  is_inner_convex U -> 0 <= M ->
  (forall a, U a -> exists L : Hom X Y,
    has_norm_differential NX NY A f a L /\ forall v, NY (L v) <= M*NX v) ->
  forall x y, U x -> U y -> NY (f x-f y) <= M*NX (x-y).
Proof.
move=> hU hM hf.
have hlocal : @is_metric_local_slope_bound R [the metricType R of real_norm_metric_space hNX]
    [the metricType R of real_norm_metric_space hNY] U f M.
  move=> x hx C hC.
  have [L [hL hb]] := hf x hx.
  have he : 0 < C-M by rewrite subr_gt0.
  have [d [hd hr]] := norm_differential_remainder hL he.
  exists d; split=> // y hy hxy.
  have hYA : A y.
    have [K [hK _]] := hf y hy.
    exact: (@norm_domain_interior_member R X NX hNX A y (norm_differential_interior hK)).
  have hshift : x+(y-x) = y by rewrite addrC subrK.
  have hsmall : NX (y-x) < d.
    change (is_true (NX (x-y) < d)) in hxy.
    by rewrite (real_seminorm_subtract hNX.1).
  have hAA : A (x+(y-x)) by rewrite hshift.
  have hrem := hr (y-x) hAA hsmall; rewrite hshift in hrem.
  change (NY (f x-f y) <= C*NX (x-y)).
  rewrite (real_seminorm_subtract hNY.1) (real_seminorm_subtract hNX.1).
  have heq : f y-f x = (f y-f x-L (y-x))+L (y-x) by rewrite subrK.
  rewrite {1}heq; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hrem (hb (y-x))) _.
  by rewrite -mulrDl subrK.
have hh := @convex_local_slope_bound_global R X NX hNX
  (real_norm_metric_space hNY) U f M hU hM hlocal.
move=> x y hx hy; exact: hh.2 x y hx hy.
Qed.
