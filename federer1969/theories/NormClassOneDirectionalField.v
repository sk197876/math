(** Federer (1969), 4.1.1, p. 346: first
    directional derivatives of C^1 compactly
    supported functions are continuous and have
    the same support bound. These supporting
    consequences use the original differential
    and operator-continuity laws of 3.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormDifferentialLinear NormDifferentialDirectional NormDifferentialLocalAgreement NormClassOneUP
  NormOpenDomainLaws SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_one_directional_continuous]: the
    actual first directional derivative is continuous,
    supporting the integral derivative in Federer
    4.1.1, p. 346. *)
Theorem norm_class_one_directional_continuous (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (f:X->Y) (D:X->Hom X Y) v:
  is_norm_class_one_field NX NY U f D ->
  norm_class_zero NX NY U (fun x=>D x v).
Proof.
move=>hF a ha; split; first exact:(@norm_class_one_zero R X Y NX NY U f D hF a ha).1.
move=>e he.
have hn:=real_seminorm_nonnegative hNX.1 v.
have hnp:0<NX v+1 by lra.
have he':0<e/(NX v+1) by rewrite divr_gt0.
have [d [hd hb]]:=norm_class_one_continuity hF ha he'.
exists d; split=>// h hh hs.
have hBound:=hb h hh hs v.
change (is_true (NY (D (a+h) v-D a v)<e)).
have hNorm:NY (D (a+h) v-D a v)<=e/(NX v+1)*NX v.
  exact hBound.
apply:le_lt_trans hNorm _.
have hLess:e/(NX v+1)*NX v<e/(NX v+1)*(NX v+1).
  by rewrite ltr_pM2l // ltrDl.
by rewrite divfK ?gt_eqF // in hLess.
Qed.

(** Source for [norm_differential_zero_off_compact]: a
    function vanishing off a compact K has zero
    differential there, supporting the compact
    derivative integral in Federer 4.1.1, p. 346. *)
Theorem norm_differential_zero_off_compact (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (K:smooth_compact_set hNX (fun _=>True)) (f:X->Y) (D:X->Hom X Y):
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  (forall x,has_norm_differential NX NY (fun _=>True) f x (D x)) ->
  forall x,~smooth_compact_carrier K x ->D x=0.
Proof.
move=>hZero hD x hx.
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K).
have hOpen:=closed_openC hClosed.
have hNear:norm_domain_interior NX (~` smooth_compact_carrier K) x.
  apply:((@norm_domain_interior_neighbourhood R X NX hNX (~` smooth_compact_carrier K) x).2).
  exact:open_nbhs_nbhs (conj hOpen hx).
have [r [hr hBall]]:=hNear.
have hConst:=@norm_differential_constant R X Y NX NY hNX hNY (fun _=>True) x 0
  (norm_full_domain_interior NX x).
have hLocal:=@norm_differential_local_agreement R X Y NX NY hNX
  (fun _=>True) (fun _=>True) (fun _=>0) f x 0 r hr
  (fun _ _=>iff_refl True) (fun h hh _=>esym (hZero _ (hBall h hh))) hConst.
exact:(norm_differential_unique hNX hNY (hD x) hLocal).
Qed.
