(** Federer (1969), 3.2.35, p. 271:
    an open neighbourhood of zero absorbs every
    vector, so the displayed Minkowski infimum is
    finite before convexity or boundedness is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra.
From Federer Require Import RealNormUP NormMetric MinkowskiGaugeUP MinkowskiGaugeExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_zero_absorbing]: the
    nonempty positive rescaling set defining g(x)
    in Federer 3.2.35, p. 271. A
    ball about zero inside S contains x/t
    for a sufficiently large positive t. This
    supporting fact works in arbitrary normed spaces
    and does not require convexity or boundedness. *)
Lemma norm_open_zero_absorbing (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set (real_norm_metric_space hN)):
  open S ->S 0 ->forall x:V,exists t:R,0<t /\S (t^-1*:x).
Proof.
move=>hOpen hZero x.
have [r hr hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (0:real_norm_metric_space hN) S) (open_nbhs_nbhs (conj hOpen hZero)).
have hNx:0<=N x:=real_seminorm_nonnegative hN.1 x.
pose t:R:=(N x+1)/r.
have hNumerator:0<N x+1 by lra.
have ht:0<t by rewrite /t divr_gt0.
have hRadius:t*r=N x+1 by rewrite /t divfK ?gt_eqF.
have hSmall:N x/t<r.
  by rewrite ltr_pdivrMr // mulrC hRadius ltrDl.
have hInv:0<t^-1 by rewrite invr_gt0.
exists t; split; first exact ht.
apply:hBall.
change (is_true (N (0-t^-1*:x)<r)).
rewrite sub0r (real_seminorm_negate hN.1)
  (real_seminorm_scale hN.1) (ger0_norm (ltW hInv)) mulrC.
exact hSmall.
Qed.

(** Source for [norm_open_minkowski_gauge_exists]:
    existence of the defining g for the open
    convex body in Federer 3.2.35, p. 271.
    Openness and zero membership alone already suffice;
    the actual infimum laws, rather than its private
    representation, are the complete conclusion used
    in subsequent convex-boundary arguments. *)
Theorem norm_open_minkowski_gauge_exists (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set (real_norm_metric_space hN)):
  open S ->S 0 ->exists g:V->R,@is_minkowski_gauge R V S g.
Proof.
move=>hOpen hZero; apply:(@minkowski_gauge_exists R V S).
exact:(@norm_open_zero_absorbing R V N hN S hOpen hZero).
Qed.
