(** Federer (1969), 1.8.1, p. 38: supporting separation for the convex-hull
    argument, using the nearest-point method of 1.7.13, p. 37. The proof
    below uses the quadratic norm expansion on a segment, without
    differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  InnerConvex InnerNearestUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_nearest_convex_variational]: Federer 1.8.1, p. 38,
    supporting convex separation lemma No completeness is needed after a
    nearest point has been supplied by its laws. *)
Theorem inner_nearest_convex_variational (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set V) (hC : is_inner_convex C) a c
    (hc : is_inner_nearest hB a C c) y : C y -> B (a-c) (y-c) <= 0.
Proof.
move=> hy; pose r := a-c; pose v := y-c; pose b := B r v; pose q := B v v.
change (b <= 0); have [hb|hb] := leP b 0 => //; exfalso.
have hq : 0 <= q := inner_nonnegative hB v.
have hden : 0 < q+b.
  apply: (lt_le_trans hb); by rewrite lerDr.
pose t := b/(q+b).
have ht : 0 < t := divr_gt0 hb hden.
have ht1 : t <= 1.
  rewrite /t (@ler_pdivrMr R (q+b) 1 b hden) mul1r lerDr; exact hq.
have hmul : t*(q+b)=b by rewrite /t divfK // gt_eqF.
have htq : t*q <= b.
  have hqb : q <= q+b by rewrite lerDl; exact: ltW hb.
  have hh := ler_wpM2l (ltW ht) hqb.
  by rewrite hmul in hh.
have hp := @hC c y (inner_nearest_member_law hc) hy t (ltW ht) ht1.
have hs := inner_nearest_minimal_law hc hp.
have hsegment : (1-t)*:c+t*:y = c+t*:(y-c).
  by rewrite scalerBl scale1r scalerBr addrAC addrA.
have he : a-((1-t)*:c+t*:y) = r+(-t)*:v.
  by rewrite hsegment /r /v opprD addrA scaleNr.
have hs2 : inner_norm hB r ^+2 <= inner_norm hB (r+(-t)*:v)^+2.
  rewrite (ler_sqr (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _)).
  by rewrite -he.
rewrite !inner_norm_sqr (inner_sum_square hB r ((-t)*:v)) (bilZr (inner_bilinear hB))
  (inner_scale_square hB) in hs2.
change (is_true (B r r <= B r r + ((-t)*b+(-t)*b)+(-t)^+2*q)) in hs2.
rewrite sqrrN !mulNr -addrA lerDl in hs2.
have hsq := ler_wpM2l (ltW ht) htq.
rewrite mulrA -expr2 in hsq.
have hh := lerD (lexx (-(t*b)+ -(t*b))) hsq.
have hcancel : -(t*b)+ -(t*b)+t*b = -(t*b) by rewrite -addrA addNr addr0.
rewrite hcancel in hh.
have hbad := le_trans hs2 hh.
rewrite oppr_ge0 in hbad.
have hpos : 0 < t*b := mulr_gt0 ht hb.
by have := lt_le_trans hpos hbad; rewrite ltxx.
Qed.
