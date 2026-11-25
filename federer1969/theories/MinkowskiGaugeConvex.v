(** Federer (1969), 3.2.35, p. 271:
    convexity of the actual Minkowski gauge follows
    from original convex-set membership and the
    independent infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import MinkowskiGaugeUP MinkowskiGaugeBasic MinkowskiGaugeHomogeneity
  InnerConvex ConvexFunctionUP ConvexPositiveRescalings.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_gauge_subadditive]: the
    convex homogeneous inequality for g following
    the displayed rescaling identity in Federer
    3.2.35, p. 271. Approximate the two
    actual infima, combine their positive rescalings,
    and remove the arbitrary positive error. *)
Lemma minkowski_gauge_subadditive (R:realType) (V:lmodType R) (S:set V) g:
  is_minkowski_gauge S g ->is_inner_convex S ->forall u v:V,g (u+v)<=g u+g v.
Proof.
move=>hG hConvex u v; apply/ler_addgt0Pr=>e he.
have hHalf:0<e/2 by rewrite divr_gt0 // ltr0n.
have [r [hr [hu hru]]]:=@minkowski_gauge_approximation R V S g hG u (e/2) hHalf.
have [s [hs [hv hsv]]]:=@minkowski_gauge_approximation R V S g hG v (e/2) hHalf.
have hMember:=convex_positive_rescaling_sum hConvex hr hs hu hv.
have hBound:=@minkowski_gauge_lower R V S g hG (u+v) (r+s)
  (addr_gt0 hr hs) hMember.
lra.
Qed.

(** Source for [minkowski_gauge_convex]: the
    assertion that g is a convex function in
    Federer 3.2.35, p. 271. Subadditivity
    and nonnegative homogeneity prove every convex
    combination inequality on the whole vector space;
    the endpoint scalar cases use actual g(0)=0. *)
Lemma minkowski_gauge_convex (R:realType) (V:lmodType R) (S:set V) g:
  is_minkowski_gauge S g ->is_inner_convex S ->S 0 ->
  is_real_convex_function_on setT g.
Proof.
move=>hG hConvex hZero; split; first by move=>x y _ _ t ht0 ht1.
move=>x y _ _ t ht0 ht1.
have hNonnegative:0<=1-t by rewrite subr_ge0.
have hBound:=minkowski_gauge_subadditive hG hConvex ((1-t)*:x) (t*:y).
by rewrite (@minkowski_gauge_nonnegative_homogeneous R V S g hG hZero (1-t) x hNonnegative)
  (@minkowski_gauge_nonnegative_homogeneous R V S g hG hZero t y ht0) in hBound.
Qed.
