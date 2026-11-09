(** Federer (1969), 3.3.21, p. 309: actual diverging counts make both the radii and the density bounds small. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ArchimedeanReciprocal NaturalNegativePowerCutoff
  DivergingCantorScheduleUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [diverging_schedule_original_sparse_scalars]: for
    every original n_j->infinity and every fixed positive k,K,p,
    both k/(3*n_j) and K*n_j^(-p) are arbitrarily small at all
    sufficiently late original levels. This supplies 3.3.21,
    p. 309, without a monotonicity or speed assumption on n. *)
Theorem diverging_schedule_original_sparse_scalars (R:realType)
    (n:nat->nat) (k K p e d:R):
  cantor_schedule_tends_infinity n ->0<k ->0<K ->0<p ->0<e ->0<d ->
  exists J,forall j,(J<=j)%N ->
    (2<=n j)%N /\k/(3 * (n j)%:R)<d /\K * real_power (n j)%:R (-p)<e.
Proof.
move=>hDiverge hk hK hp he hd.
have hTarget:0<3 * d/k by rewrite divr_gt0 // mulr_gt0 // ltr0n.
have [q hq]:=real_reciprocal_below hTarget.
have [N [hN hSmall]]:=natural_negative_power_eventually_small hp hK he.
have [J hJ]:=hDiverge (maxn N q.+1).
exists J=>j hj.
have hNj:(N<=n j)%N:=leq_trans (leq_maxl _ _) (hJ j hj).
have hQ:(q.+1<=n j)%N:=leq_trans (leq_maxr _ _) (hJ j hj).
have hCount:(2<=n j)%N:=leq_trans hN hNj.
have hReal:(q.+1%:R<=(n j)%:R:>R) by rewrite ler_nat.
have hNPos:0<((n j)%:R:R) by rewrite ltr0n;exact:leq_trans (leqnSn 1) hCount.
have hQPos:0<(q.+1%:R:R) by rewrite ltr0n.
have hInv:((n j)%:R:R)^-1<=(q.+1%:R:R)^-1 by rewrite lef_pV2 ?posrE.
have hSmallInverse:((n j)%:R:R)^-1<3 * d/k:=le_lt_trans hInv hq.
have hRadius:k/(3 * (n j)%:R)<d.
  have hThree:0<(3:R) by rewrite ltr0n.
  have hDen:0<3 * (n j)%:R:=mulr_gt0 hThree hNPos.
  have hThreeD:((n j)%:R:R)^-1 * k<3 * d.
    by move:hSmallInverse;rewrite (ltr_pdivlMr _ _ hk).
  have hScaled:((n j)%:R:R)^-1 * k * (n j)%:R<3 * d * (n j)%:R.
    by rewrite (ltr_pM2r hNPos).
  have hLeft:((n j)%:R:R)^-1 * k * (n j)%:R=k by rewrite mulrAC mulVf ?gt_eqF // mul1r.
  rewrite hLeft in hScaled.
  rewrite (ltr_pdivrMr _ _ hDen);nra.
split;first exact:hCount.
split;[exact:hRadius|exact:hSmall (n j) hNj].
Qed.
