(** Federer (1969), 4.1.2, p. 348: sufficiently
    small Borel cells approximate all translated kernel
    integrands uniformly on a compact set of centres.
    This is the uniformity used after differentiating
    the original finite sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormMetricSubtractContinuity
  NormCompactFunctionBound CompactNearbyUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_kernel_field_oscillation]: compact-uniform
    closeness of the original kernel integrands in
    Federer 4.1.2, p. 348. The
    target has arbitrary dimension; no normed function
    space or new integration construction is introduced. *)
Theorem compact_kernel_field_oscillation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (C K:set X) (theta:X->R) (f:X->Y):
  compact [set x:real_norm_metric_space hNX|C x] ->
  compact [set x:real_norm_metric_space hNX|K x] ->
  norm_class_zero NX (fun t:R^o=>`|t|) (fun _=>True) theta ->
  norm_class_zero NX NY (fun _=>True) f ->
  forall eta:R,0<eta ->exists d:R,0<d /\ forall x z w,
    C x ->K z ->K w ->NX (z-w)<d ->
    NY (theta (x-z)*:f z-theta (x-w)*:f w)<eta.
Proof.
move=>hC hK hTheta hF eta hEta.
pose T:=real_norm_metric_space hNX.
pose A:set T:=(fun p:T*T=>(p.1-p.2:T)) @`
  ([set x:T|C x] `*` [set z:T|K z]).
have hA:compact A.
  exact:(continuous_compact
    (continuous_subspaceT (@real_norm_metric_subtract_continuous R X NX hNX))
    (compact_setX hC hK)).
have hMember x z:C x ->K z ->A (x-z).
  move=>hx hz; exists (x,z); by split.
have[MTheta [hMTheta hThetaBound]]:=@norm_class_zero_compact_bounded R X R^o NX
  (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) (fun _=>True) A theta hA
  (fun _ _=>Logic.I) hTheta.
have[MF [hMF hFBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  (fun _=>True) K f hK (fun _ _=>Logic.I) hF.
have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hEF:0<(eta/2)/MTheta by rewrite divr_gt0.
have hET:0<(eta/2)/MF by rewrite divr_gt0.
have[dF [hdF hNearF]]:=@norm_class_zero_compact_uniform_nearby R X Y NX NY hNX hNY
  (fun _=>True) K f hK (fun _ _=>Logic.I) hF ((eta/2)/MTheta) hEF.
have[dT [hdT hNearT]]:=@norm_class_zero_compact_uniform_nearby R X R^o NX (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) (fun _=>True) A theta hA
  (fun _ _=>Logic.I) hTheta ((eta/2)/MF) hET.
exists (Num.min dF dT); split; first by rewrite lt_min hdF hdT.
move=>x z w hx hz hw; rewrite lt_min=>/andP [hzwF hzwT].
have hFSmall:=hNearF w z hw Logic.I hzwF.
have hId:(x-z)-(x-w)=w-z.
  by rewrite opprB addrA (addrAC x (-z) w) (addrAC (x+w) (-z) (-x))
    (addrAC x w (-x)) subrr add0r.
have hArgument:NX ((x-z)-(x-w))<dT.
  by rewrite hId (real_seminorm_subtract hNX.1).
have hTSmall:=hNearT (x-w) (x-z) (hMember x w hx hw) Logic.I hArgument.
have hFScaled:MTheta*NY (f z-f w)<eta/2.
  have h:MTheta*NY (f z-f w)<MTheta*((eta/2)/MTheta) by rewrite ltr_pM2l.
  have hCancel:MTheta*((eta/2)/MTheta)=eta/2 by rewrite mulrC divfK // gt_eqF.
  by rewrite hCancel in h.
have hTScaled:MF*`|theta (x-z)-theta (x-w)|<eta/2.
  have h:MF*`|theta (x-z)-theta (x-w)|<MF*((eta/2)/MF) by rewrite ltr_pM2l.
  have hCancel:MF*((eta/2)/MF)=eta/2 by rewrite mulrC divfK // gt_eqF.
  by rewrite hCancel in h.
have hSplit:theta (x-z)*:f z-theta (x-w)*:f w=
    theta (x-z)*:(f z-f w)+(theta (x-z)-theta (x-w))*:f w.
  by rewrite scalerBr scalerBl addrA subrK.
rewrite hSplit.
apply:le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
rewrite !(real_seminorm_scale hNY.1).
have hFirst:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (f z-f w))
  (hThetaBound (x-z) (hMember x z hx hz)).
have hSecond:=ler_wpM2l (normr_ge0 (theta (x-z)-theta (x-w))) (hFBound w hw).
nra.
Qed.
