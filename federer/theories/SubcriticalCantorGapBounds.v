(** Federer (1969), 3.2.40, p. 276: supporting
    positive gap estimates for the actual subcritical and
    critical equal-cost Cantor subdivisions. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RealPower CantorSplitRadiusUP CantorSplitRadius
  PowerCantorSubcriticalSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [subcritical_cantor_split_gap_bounds]: supporting
    separated-point tube lower estimates in Federer 3.2.40,
    p. 276. The actual gap t-s lies between d/n and d,
    is positive and exceeds the child width. These are
    consequences of the original cost laws, not extra
    hypotheses on the Cantor example or its schedule. *)
Lemma subcritical_cantor_split_gap_bounds (R:realType) (c m d s:R) (n:nat):
  0<c ->0<m ->m<=1/2 ->0<d ->(2<=n)%N ->
  is_cantor_split_radius (fun t=>c*real_power t m) d n s ->
  let g:=cantor_split_spacing d n s-s in
  d/n%:R<=g /\0<g /\s<g /\g<=d.
Proof.
move=>hc hm hmHalf hd hn hSplit g.
have hN:(0<(n%:R:R)) by rewrite ltr0n; exact:leq_trans (leqnSn 1) hn.
have hN2:((2:R)<=n%:R) by rewrite ler_nat.
have hDen:(0<(n%:R-1:R)) by lra.
have hDen1:(1<=(n%:R-1:R)) by lra.
have hS:0<s:=(cantor_split_radius_bounds hSplit).1.
have hChild:=@subcritical_power_cantor_child_square_bound R c m d s n hc hm hmHalf hd hn hSplit.
have hScaled:=ler_wpM2l (ltW hN) hChild.
have hCancel:(n%:R*(d/(n%:R)^+2):R)=d/n%:R by field; rewrite (gt_eqF hN).
rewrite hCancel in hScaled.
have hGapProduct:g*(n%:R-1)=d-n%:R*s.
  by rewrite /g /cantor_split_spacing; field; rewrite (gt_eqF hDen).
have hParentProduct:(d/n%:R)*(n%:R-1)=d-d/n%:R by field; rewrite (gt_eqF hN).
have hLower:d/n%:R<=g.
  rewrite -(ler_pM2r hDen) hGapProduct hParentProduct.
  lra.
have hParentPositive:0<d/n%:R by rewrite divr_gt0.
have hGapPositive:0<g:=lt_le_trans hParentPositive hLower.
have hChildGap:s<g:=lt_le_trans (cantor_split_radius_bounds hSplit).2 hLower.
pose t:=cantor_split_spacing d n s.
have hInvDen:0<((n%:R:R)-1)^-1 by rewrite invr_gt0.
have hSpacing:t<d/(n%:R-1).
  rewrite /t /cantor_split_spacing (ltr_pM2r hInvDen).
  lra.
have hParentUpper:d/(n%:R-1)<=d.
  rewrite ler_pdivrMr //.
  have h:=ler_wpM2l (ltW hd) hDen1.
  by rewrite mulr1 in h.
have hGapSpacing:g<=t by rewrite /g /t; lra.
split=>//; split=>//; split=>//.
exact:le_trans hGapSpacing (le_trans (ltW hSpacing) hParentUpper).
Qed.
