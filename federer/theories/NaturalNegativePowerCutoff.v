(** Federer (1969), 3.3.21, p. 309: diverging original subdivision counts make negative powers small. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ArchimedeanReciprocal RealPower RealPowerContinuity RealPowerDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [natural_negative_power_eventually_small]: an actual
    positive fixed coefficient times N^(-p) becomes arbitrarily small
    for all sufficiently large natural N when p>0. This supplies
    the original n_j->infinity step in 3.3.21, p. 309, without
    requiring a monotone or specially rapid original schedule. *)
Theorem natural_negative_power_eventually_small (R:realType) (p K e:R):
  0<p ->0<K ->0<e ->exists N:nat,(2<=N)%N /\forall n,(N<=n)%N ->
    K * real_power n%:R (-p)<e.
Proof.
move=>hp hK he.
pose t:=real_power (e/K) p^-1.
have hEK:0<e/K by rewrite divr_gt0.
have ht:0<t:=real_power_strictly_positive _ hEK.
have hPower:real_power t p=e/K by rewrite /t real_power_inverse_power ?ltW.
have [q hq]:=real_reciprocal_below ht.
pose N:=maxn 2 q.+1.
exists N;split;first exact:leq_maxl.
move=>n hNn.
have hTwo:(2<=n)%N:=leq_trans (leq_maxl 2 q.+1) hNn.
have hn:0<(n%:R:R) by rewrite ltr0n;exact:leq_trans (leqnSn 1) hTwo.
have hQ:(q.+1<=n)%N:=leq_trans (leq_maxr 2 q.+1) hNn.
have hQR:(q.+1%:R<=n%:R:>R) by rewrite ler_nat.
have hQP:0<(q.+1%:R:R) by rewrite ltr0n.
have hInv:(n%:R:R)^-1<=(q.+1%:R:R)^-1 by rewrite lef_pV2 ?posrE.
have hSmall:(n%:R:R)^-1<t:=le_lt_trans hInv hq.
have hStrict:real_power ((n%:R:R)^-1) p<e/K.
  have hInversePositive:0<(n%:R:R)^-1 by rewrite invr_gt0.
  rewrite -hPower;exact:real_power_strict_monotone (ltW hInversePositive) hSmall hp.
rewrite real_power_inverse_base // -real_power_negative_exponent // in hStrict.
by move:hStrict;rewrite ltr_pdivlMr // mulrC.
Qed.
