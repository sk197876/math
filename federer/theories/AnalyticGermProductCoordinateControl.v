(** Federer (1969), 3.4.5, p. 319: finitely
    many original derivative coordinates control each coordinate
    of multiplication. The finite Leibniz estimate discharges
    the analytic continuity claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermGrowthUP
  AnalyticGermJetNormLaws AnalyticGermProductVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_product_finite_coordinate_control]:
    the finite-coordinate continuity estimate for the original
    product in 3.4.5, p. 319. The tolerance
    is proved to exist from the finite Leibniz sum;
    no product-continuity hypothesis is added. *)
Theorem analytic_germ_product_finite_coordinate_control (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha0 beta0:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]) (epsilon:R):
  0<epsilon ->exists delta:R,0<delta /\forall alpha beta,
    (forall i,(i<=m)%N ->@analytic_germ_jet_norm R X NX hNX a i (alpha-alpha0)<=delta) ->
    (forall i,(i<=m)%N ->@analytic_germ_jet_norm R X NX hNX a i (beta-beta0)<=delta) ->
    @analytic_germ_jet_norm R X NX hNX a m (alpha*beta-alpha0*beta0)<epsilon.
Proof.
move=>hEpsilon.
pose JN:=@analytic_germ_jet_norm R X NX hNX a.
have hJN i alpha:0<=JN i alpha:=@analytic_germ_jet_norm_nonnegative R X NX hNX a i alpha.
pose L:R:=\sum_(j<m.+1) ('C(m,m-j))%:R*(JN j beta0+1+JN (m-j)%N alpha0).
have hL:0<=L.
  apply:sumr_ge0=>j _;apply:mulr_ge0;first exact:ler0n.
  exact:addr_ge0 (addr_ge0 (hJN j beta0) ler01) (hJN (m-j)%N alpha0).
have hDen:0<L+1 by rewrite addrC ltr_pwDl.
pose delta:=Num.min 1 (epsilon/(L+1)).
have hDelta:0<delta by rewrite /delta lt_min ltr01 divr_gt0.
have hDeltaOne:delta<=1 by rewrite /delta ge_min lexx orTb.
have hDeltaRatio:delta<=epsilon/(L+1) by rewrite /delta ge_min lexx orbT.
have hFactor:delta*(L+1)<=epsilon.
  have hh:=ler_wpM2r (ltW hDen) hDeltaRatio.
  by rewrite divfK ?gt_eqF in hh.
have hStrict:delta*L<epsilon.
  apply:lt_le_trans _ hFactor.
  by rewrite ltr_pM2l // ltrDl ltr01.
exists delta;split;first exact:hDelta.
move=>alpha beta hAlpha hBeta.
have hVariation:=@analytic_germ_product_jet_variation R X NX hNX a m alpha beta alpha0 beta0.
apply:le_lt_trans hVariation _.
apply:le_lt_trans _ hStrict.
have hBetaBound i (hi:(i<=m)%N):JN i beta<=JN i beta0+1.
  have hIdentity:beta=beta0+(beta-beta0) by rewrite addrC subrK.
  rewrite {1}hIdentity.
  apply:le_trans (@analytic_germ_jet_norm_add R X NX hNX a i beta0 (beta-beta0)) _.
  exact:lerD (lexx _) (le_trans (hBeta i hi) hDeltaOne).
rewrite /L mulr_sumr;apply:ler_sum=>j _.
have hj:(j<=m)%N:=ltn_ord j.
have hSub:(m-j<=m)%N:=leq_subr j m.
have hFirst:JN (m-j)%N (alpha-alpha0)*JN j beta<=delta*(JN j beta0+1).
  exact:ler_pM (hJN (m-j)%N (alpha-alpha0)) (hJN j beta) (hAlpha _ hSub) (hBetaBound j hj).
have hSecond:JN (m-j)%N alpha0*JN j (beta-beta0)<=JN (m-j)%N alpha0*delta.
  exact:ler_pM (hJN (m-j)%N alpha0) (hJN j (beta-beta0)) (lexx _) (hBeta j hj).
have hBoth:=ler_wpM2r (ler0n R ('C(m,m-j))) (lerD hFirst hSecond).
rewrite ![_ * ('C(m,m-j))%:R]mulrC in hBoth.
have hEqual:('C(m,m-j))%:R*(delta*(JN j beta0+1)+JN (m-j)%N alpha0*delta)=
    delta*(('C(m,m-j))%:R*(JN j beta0+1+JN (m-j)%N alpha0)) by ring.
by rewrite hEqual in hBoth.
Qed.
