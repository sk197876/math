(** Federer (1969), 4.1.14, p. 370: the restriction of the
    original locally Lipschitzian f to a compact part of its open
    domain is Lipschitzian. This supporting adapter applies the
    registered finite-cover argument of 2.2.7, p. 64, on the original
    open domain; it does not assume a globally locally Lipschitz extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormCompactFunctionBound CoveringFamilyUP MetricClosedBalls
  LipschitzUP LipschitzBasic MetricCompactLocalLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_local_lipschitz_class_zero]: the continuity
    implicit in the original local Lipschitz hypothesis, Federer
    4.1.14, p. 370, by the definition in 2.2.7, p. 64. Arbitrary
    values of the total representative outside U play no role. *)
Theorem norm_open_local_lipschitz_class_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (f:X->Y):
  (forall x,U x->norm_domain_interior NX U x) ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f ->norm_class_zero NX NY U f.
Proof.
move=>hU hLocal a ha;split;first exact:hU a ha.
have[V [hV [L [hL hBound]]]]:=hLocal a ha.
have hVa:V a:=nbhs_singleton hV.
have[r hr hBall]:=(metricType_numDomainType.nbhs_mdistP
  (a:real_norm_metric_space hNX) V).1 hV.
move=>eta hEta.
exists (Num.min r (eta/L));split;first by rewrite lt_min hr divr_gt0.
move=>h hAh;rewrite lt_min=>/andP[hNear hSmall].
have hVah:V (a+h).
  apply:hBall.
  change (is_true (NX (a-(a+h))<r)).
  by rewrite opprD addrA subrr add0r (real_seminorm_negate hNX.1).
have hEstimate:=hBound.2 (a+h) a (conj hAh hVah) (conj ha hVa).
have hDifference:(a+h)-a=h by rewrite (addrC a h) addrK.
change (is_true (NY (f (a+h)-f a)<=L*NX ((a+h)-a))) in hEstimate.
rewrite hDifference in hEstimate.
apply:le_lt_trans hEstimate _.
by rewrite mulrC -ltr_pdivlMr.
Qed.

(** Source for [norm_open_local_lipschitz_compact]: the compact
    Lipschitz bound used for the smoothing construction in Federer
    4.1.14, p. 370. The registered metric theorem handles both nearby
    and separated pairs. K may be empty, disconnected or a singleton. *)
Theorem norm_open_local_lipschitz_compact (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (f:X->Y) (K:set (real_norm_metric_space hNX)):
  (forall x,U x->norm_domain_interior NX U x) ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f ->compact K ->K `<=` U ->
  @is_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) K f.
Proof.
move=>hU hLocal hK hKU.
have hContinuous:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY
  U f hU hLocal.
have[M [hM hImage]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  U K f hK hKU hContinuous.
apply:(@metric_compact_local_lipschitz R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) K f (M+M) hK (addr_ge0 (ltW hM) (ltW hM))).
- move=>x y hx hy.
  change (is_true (NY (f x-f y)<=M+M)).
  have hTriangle:=real_seminorm_triangle hNY.1 (f x) (-f y).
  rewrite (real_seminorm_negate hNY.1) in hTriangle.
  exact:(le_trans hTriangle (lerD (hImage x hx) (hImage y hy))).
- move=>c hc.
  have hUc:=hKU c hc.
  have[V [hV [L [hL hBound]]]]:=hLocal c hUc.
  have[r hr hVBall]:=(metricType_numDomainType.nbhs_mdistP
    (c:real_norm_metric_space hNX) V).1 hV.
  have[s [hs hUBall]]:=hU c hUc.
  exists (Num.min r s),L;split;first by rewrite lt_min hr hs.
  apply:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (U `&` V)
    (@metric_open_ball R (real_norm_metric_space hNX) c (Num.min r s)) f L _ hBound).
  move=>x hx.
  change (is_true (NX (c-x)<Num.min r s)) in hx.
  move:hx;rewrite lt_min=>/andP[hxr hxs].
  split.
  + have hSmall:NX (x-c)<s by rewrite (real_seminorm_subtract hNX.1).
    have h:=hUBall (x-c) hSmall.
    by rewrite (addrC c (x-c)) subrK in h.
  + apply:hVBall;exact:hxr.
Qed.
