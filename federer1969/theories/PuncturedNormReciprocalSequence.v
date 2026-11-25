(** Federer (1969), 4.1.2, p. 347: actual two-sided
    directional derivative limits hold along the positive reciprocal
    increments used to prove measurability and dominated convergence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormedCurveDerivativeUP
  ExtendedRealOrderLimit RealErrorOrderLimit ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [punctured_norm_reciprocal_sequence]: the measurable
    difference-quotient sequence for the original D_j f in
    Federer 4.1.2, p. 347, retains its actual norm limit. *)
Theorem punctured_norm_reciprocal_sequence (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (u:R->Y) (v:Y):
  punctured_norm_limit NY u v ->
  (fun m:nat=>(u (((m.+1)%:R:R)^-1):real_norm_metric_space hNY)) @ \oo -->
    (v:real_norm_metric_space hNY).
Proof.
move=>hLimit V hV.
have[eta hEta hBall]:=(metricType_numDomainType.nbhs_mdistP (v:real_norm_metric_space hNY) V).1 hV.
have[d [hd hBound]]:=hLimit eta hEta.
have[N hN]:=@extended_finite_order_limit_error R
  (fun m:nat=>((m.+1)%:R:R)^-1) 0 d (@reciprocal_natural_order_limit R) hd.
exists N; first exact Logic.I.
move=>m hmN; apply:hBall.
change (is_true (NY (v-u (((m.+1)%:R:R)^-1))<eta)).
rewrite (real_seminorm_subtract hNY.1); apply:hBound.
have hPositive:0<((m.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
have hSmall:=hN m hmN.
rewrite subr0 (ger0_norm (ltW hPositive)) in hSmall.
by rewrite (ger0_norm (ltW hPositive)); apply/andP; split.
Qed.
