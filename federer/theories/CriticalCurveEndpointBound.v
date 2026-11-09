(** Federer (1969), 3.4.2(6), p. 312: the endpoint estimate for
    f composed with the original retracted segment. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialConvexBound InnerConvex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_curve_positive_parameter_bound]: supporting
    the final mean-value step in 3.4.2(6), p. 312. The derivative bound
    is needed only at positive parameters; differentiability at zero
    supplies continuity there. The proof applies 2.2.7 on [delta,1]
    and lets delta decrease to zero. No completeness or finite target
    dimension is required. *)
Theorem critical_curve_positive_parameter_bound (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (A:R^o->Prop) (q:R->Y) (C:R):
  0<=C ->norm_differentiable_at (fun t:R^o=>`|t|) NY A q 0 ->
  (forall t:R,0<t ->t<=1 ->exists L:Hom R^o Y,
    has_norm_differential (fun s:R^o=>`|s|) NY A q t L /\
    forall s:R^o,NY (L s)<=C*`|s|) ->
  NY (q 1-q 0)<=C.
Proof.
move=>hC [L0 h0] hDiff;apply/negPn/negP=>hBad.
have hGap:C<NY (q 1-q 0) by rewrite ltNge.
pose e:=(NY (q 1-q 0)-C)/2.
have he:0<e by rewrite /e divr_gt0 // subr_gt0.
have [r [hr hNear]]:=norm_differential_continuous_at hNY h0 he.
pose delta:=Num.min (r/2) (1/2).
have hd:0<delta by rewrite /delta lt_min !divr_gt0 //.
have hdSmall:delta<r.
  have hh:delta<=r/2 by rewrite /delta ge_min lexx.
  lra.
have hdOne:delta<1.
  have hh:delta<=(1/2:R) by rewrite /delta ge_min lexx orbT.
  lra.
have [Ld [hDd _]]:=hDiff delta hd (ltW hdOne).
have hAd:A delta:=norm_domain_interior_member (@scalar_absolute_value_norm R)
  (norm_differential_interior hDd).
have hNearD:NY (q delta-q 0)<e.
  have hh:=hNear delta.
  rewrite add0r in hh.
  apply:hh;first exact:hAd.
  by rewrite (ger0_norm (ltW hd)).
pose B:=fun t:R^o=>delta<=t /\t<=1.
have hConvex:is_inner_convex B.
  move=>x y [hx0 hx1] [hy0 hy1] t ht0 ht1.
  change (delta<=(1-t)*x+t*y /\(1-t)*x+t*y<=1).
  split;nra.
have hD t (ht:B t):exists L:Hom R^o Y,
    has_norm_differential (fun s:R^o=>`|s|) NY A q t L /\
    forall s:R^o,NY (L s)<=C*`|s|.
  exact:(hDiff t (lt_le_trans hd ht.1) ht.2).
have hMean:=@norm_differential_convex_bound R R^o Y
  (fun t:R^o=>`|t|) NY (@scalar_absolute_value_norm R) hNY A B q C
  hConvex hC hD 1 delta (conj (ltW hdOne) (lexx 1))
  (conj (lexx delta) (ltW hdOne)).
have hAbs:`|1-delta|<=1 by rewrite ger0_norm;nra.
have hBound:NY (q 1-q delta)<=C.
  apply:(le_trans hMean).
  have hh:=ler_wpM2l hC hAbs;by rewrite mulr1 in hh.
have hTriangle:=real_seminorm_triangle hNY.1 (q 1-q delta) (q delta-q 0).
rewrite addrA subrK in hTriangle.
rewrite /e in hNearD;nra.
Qed.
