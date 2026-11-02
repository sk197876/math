(** Private cutoff existence for Federer (1969), 3.1.23,
    pp. 236–237. Only the seal and audit may import this
    construction. A squared-norm profile ensures smoothness at zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerNormInequalities
  HilbertFormCompactness LinearBasis FiniteNormMetricCompactness NormDifferentialUP NormDifferentialDirectional
  NormOpenDomainLaws ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialFirst NormOperatorNormUP
  NormRegularity NormRegularityOperations NormClassInfinityQuadratic NormCompactSupportHigherBound
  ScalarUnitCutoffUP ScalarUnitCutoffSealed ScalarUnitCutoffSmooth InnerSmoothUnitBump AnnularCutoffUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_annular_cutoff_exists]: existence of the
    smooth radial cutoff used by Federer 3.1.23, pp. 236–237,
    together with a finite derivative bound. Use the already
    sealed scalar cutoff at (|x|^2-t^2)/(1-t^2). Compactness of
    the unit ball bounds its first differential. This choice
    has the printed plateau and support and avoids differentiating
    the norm at zero. No downstream proof uses this formula. *)
Theorem norm_annular_cutoff_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) t :
  0<t<1 -> exists (u:X->R^o) C,
    is_norm_annular_cutoff (inner_norm_real_norm hB) t u C.
Proof.
move=>ht.
pose N:= inner_norm hB.
pose hN:= inner_norm_real_norm hB.
pose A:= fun s:R^o=>`|s|.
pose hA:= scalar_absolute_value_norm R.
pose Z:= fun j=>@ContinuousMultilinear.space R j X R^o N A hN hA.
pose ev:= fun j=>@ContinuousMultilinear.evaluation R j X R^o N A hN hA.
pose ZN:= fun j=>@ContinuousMultilinear.norm R j X R^o N A hN hA.
pose hZ:= fun j=>@ContinuousMultilinear.laws R j X R^o N A hN hA.
pose P:= fun j=>@ContinuousMultilinear.space R j R^o R^o A A hA hA.
pose ep:= fun j=>@ContinuousMultilinear.evaluation R j R^o R^o A A hA hA.
pose PN:= fun j=>@ContinuousMultilinear.norm R j R^o R^o A A hA hA.
pose hP:= fun j=>@ContinuousMultilinear.laws R j R^o R^o A A hA hA.
pose d:= 1-t^+2.
have hd:0<d by have [ht0 ht1]:= andP ht; rewrite /d; nra.
pose q:= fun x=>(B x x-t^+2)/d.
pose u:= fun x=>@ScalarUnitCutoff.value R (q x).
have hcut:=@ScalarUnitCutoff.laws R.
have hinner x (hx:N x<=t):u x= 1.
  apply: (scalar_unit_cutoff_lower hcut).
  rewrite /q -(@inner_norm_sqr R X B hB x) ler_pdivrMr // mul0r.
  change (is_true ((N x)^+2-t^+2<=0)).
  have hn:0<=N x:=inner_norm_nonnegative hB x; have ht0:0<t:=(andP ht).1; nra.
have houter x (hx:1<=N x):u x= 0.
  apply: (scalar_unit_cutoff_upper hcut).
  rewrite /q -(@inner_norm_sqr R X B hB x) ler_pdivlMr // mul1r /d.
  change (is_true (1-t^+2<=(N x)^+2-t^+2)); nra.
have hsmooth:norm_class_all_orders hN hA (fun _=>True) u.
  move=>k.
  have hquad:=@norm_class_infinity_quadratic R X R^o N A hN hA Z ev ZN hZ
    (fun _=>True) B (fun x _=>norm_full_domain_interior N x)
    (inner_product_squared_norm_specification hB).1 k.
  have hc:=@norm_class_constant R X R^o N A hN hA (fun _=>True)
    (-t^+2) k (fun x _=>norm_full_domain_interior N x).
  have hsum:= norm_class_add hquad hc.
  have hscale:= norm_class_scale d^-1 hsum.
  have hq:norm_class hN hA (fun _=>True) q k.
    apply: (norm_class_domain_agreement _ hscale)=>x _.
    change (d^-1*(B x x-t^+2)=(B x x-t^+2)/d); ring.
  have hg:=@scalar_unit_cutoff_class_infinity R P ep PN hP k.
  exact (@norm_class_compose_on R X R^o R^o N A A hN hA hA
    (fun _=>True) (fun _=>True) q (@ScalarUnitCutoff.value R) k
    (fun _ _=>Logic.I) hq hg).
pose K:= fun x=>N x<=1.
have hK:=@finite_norm_metric_ball_compact R X N hN n e he 1.
have hz x (hx:~K x):u x= 0.
  apply: houter; apply: ltW; rewrite ltNge; by apply/negP.
have [D [C [hD [hC [hbound hzero]]]]]:=
  @norm_compact_support_higher_differential_bound R X R^o N A hN hA Z ev ZN hZ
    K u 1 hK hz (hsmooth 1%N).
exists u,C; constructor.
- move=>x; exact (scalar_unit_cutoff_bounds hcut (q x)).
- exact hinner.
- exact houter.
- move=>x y hxy; rewrite /u /q -!(@inner_norm_sqr R X B hB) hxy.
  by [].
- exact hsmooth.
- exact hC.
- move=>x L hL v.
  have hfirst:=(@norm_higher_differential_first R X R^o N A hN hA Z ev ZN hZ
    (fun _=>True) u x (D x)).1 (hD x).
  have heq:= norm_differential_unique hN hA hL hfirst.
  rewrite heq.
  have hb:= norm_operator_bound (continuous_multilinear_one_norm_laws (hZ 1%N) (D x)) v.
  apply: le_trans hb _.
  apply: ler_wpM2r; first exact (real_seminorm_nonnegative hN.1 v).
  exact (hbound x).
Qed.
