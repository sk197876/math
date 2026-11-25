(** Federer (1969), 3.3.19, p. 306: prove
    existence of local angular and radius-ratio cutoffs
    for strict tangential packing of original children. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp lra ring.
From Federer Require Import RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed
  CircularHalfPeriodStrict CircularSmallSineAbsoluteSecant NaturalScaledReciprocalTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Window.
Variable R:realType.
Local Notation p:=(@CircularTrigonometry.half_period R).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation ht:=(@CircularTrigonometry.laws R).
Local Notation hb:=(circular_trig_basic ht).

(** Source for [circular_tangent_packing_window_exists]:
    proved positive local angular window d, radius-ratio
    cutoff q and integer J give unit sine secants with
    slope kappa, a cosine margin 6q<1-cos(d), and
    actual late child coefficient 2pi kappa(1-1/n)>6.
    These are local existence witnesses supporting the last
    density claim in 3.3.19, p. 306; no cutoff or
    spacing estimate is assumed for the example. *)
Theorem circular_tangent_packing_window_exists:
  exists (kappa d q:R) (J:nat),
    0<kappa /\kappa<1 /\0<d /\d<=p /\0<q /\6* q<1-C d /\
    (forall a b:R,`|a|<=d ->`|b|<=d ->kappa*`|a-b|<=`|S a-S b|) /\
    forall n,(J<=n)%N ->(4<=n)%N /\(n%:R:R)^-1<q /\
      6<2* p* kappa*(1-n%:R^-1).
Proof.
have hp3:= @circular_half_period_strictly_above_three R.
have hp:0<p by lra.
have hpN:p!=0 by rewrite gt_eqF.
pose kappa:=(p+3)/(2* p).
have hDen:0<2* p by lra.
have hK:0<kappa by rewrite /kappa divr_gt0 //;lra.
have hK1:kappa<1 by rewrite /kappa ltr_pdivrMr //;lra.
have hIdentity:p* kappa=(p+3)/2 by rewrite /kappa;field.
have hMargin:0<2* p* kappa-6 by nra.
have [d0 [hd0 hSecant]]:= @circular_small_sine_absolute_secant R kappa hK hK1.
pose d:= Num.min d0 (p/4).
have hQuarter:0<p/4 by lra.
have hd:0<d by rewrite /d lt_min hd0 hQuarter.
have hdd0:d<=d0 by rewrite /d ge_min lexx.
have hdp4:d<=p/4 by rewrite /d ge_min lexx orbT.
have hdp:d<=p by lra.
have hZero:0<=(0:R):= lexx 0.
have hp0:0<=p:= ltW hp.
have hd0weak:0<=d:= ltW hd.
have hStrict:= @circular_trig_cosine_decreases R S C (@CircularTrigonometry.arcsine R)
  (@CircularTrigonometry.arccosine R) p ht 0 d hZero hp0 hd0weak hdp hd.
rewrite (real_cosine_zero hb) in hStrict.
have hGap:0<1-C d by lra.
pose q:= Num.min (1/16) ((1-C d)/24).
have hSixteenth:0<(1:R)/16 by lra.
have hGapPart:0<(1-C d)/24 by lra.
have hq:0<q by rewrite /q lt_min hSixteenth hGapPart.
have hqGap:q<=(1-C d)/24 by rewrite /q ge_min lexx orbT.
have hGapRatio:6* q<1-C d by lra.
have hOne:0<(1:R):= ltr01.
have hCoefficient:0<2* p* kappa by nra.
have [J1 hJ1]:= @natural_scaled_reciprocal_tail R 1 q hOne hq.
have [J2 hJ2]:= @natural_scaled_reciprocal_tail R (2* p* kappa) (2* p* kappa-6) hCoefficient hMargin.
exists kappa,d,q,(maxn 4 (maxn J1 J2));split=>//;split=>//;split=>//;split=>//;split=>//;split=>//;split.
- move=>a b ha hbnd;exact:hSecant a b (le_trans ha hdd0) (le_trans hbnd hdd0).
- move=>n hn.
  have hn4:(4<=n)%N:= leq_trans (leq_maxl 4 (maxn J1 J2)) hn.
  have hn1:(J1<=n)%N:= leq_trans (leq_trans (leq_maxl J1 J2) (leq_maxr 4 (maxn J1 J2))) hn.
  have hn2:(J2<=n)%N:= leq_trans (leq_trans (leq_maxr J1 J2) (leq_maxr 4 (maxn J1 J2))) hn.
  have [_ hSmall1]:= hJ1 n hn1.
  have [_ hSmall2]:= hJ2 n hn2.
  rewrite div1r in hSmall1.
  split=>//;split=>//;nra.
Qed.
End Window.
