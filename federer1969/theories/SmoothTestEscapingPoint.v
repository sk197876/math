(** Federer (1969), 4.1.1, p. 344: the
    corrected nonembedding proof uses compact tests outside
    any prescribed compact set with one prescribed value.
    The original smooth partition cutoff supplies them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  NormRegularity NormRegularityOperations NormRegularityBilinear CompactSupportFunctionUP
  SmoothCompactSet SmoothCompactCutoffUP SmoothCompactCutoffSealed SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothTestCompactRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestEscapingPoint.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).

(** Source for [smooth_test_escaping_point_exists]: for
    a in U minus K there is an actual
    test supported in U minus K with value
    y at a, supporting the corrected nonembedding
    assertion in Federer 4.1.1, p. 344. *)
Theorem smooth_test_escaping_point_exists (K:smooth_compact_set hNX U) a (y:Y):
  U a ->~smooth_compact_carrier K a ->
  exists f:DT,value f a=y /\ (support f `<=` (U `&` ~` smooth_compact_carrier K)).
Proof.
move=>ha hNo.
pose W:=U `&` ~` smooth_compact_carrier K.
have hOpenU:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact ((@norm_domain_interior_neighbourhood R X NX hNX U x).1 (@hU x hx)).
have hClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact K).
have hOpenW:@open (real_norm_metric_space hNX) W:=openI hOpenU (closed_openC hClosed).
have hW x (hx:W x):norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:open_nbhs_nbhs (conj hOpenW hx).
pose A:=@smooth_compact_singleton R X NX hNX W a (conj ha hNo).
pose chi:=@SmoothCompactCutoff.value R X NX hNX d b hb W A hW.
have hChi:=@SmoothCompactCutoff.laws R X NX hNX d b hb W A hW.
have [V [hV [hAV hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
have hChiA:chi a= 1:=hOne a (hAV a (erefl a)).
pose C:=@Build_smooth_compact_set R X NX hNX U
  (@real_function_support R (real_norm_metric_space hNX) chi)
  (fun x hx=>(smooth_cutoff_support_in_domain hChi hx).1) (smooth_cutoff_compact hChi).
have hScalar:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U chi.
  move=>k; exact:(@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) (fun _=>True) U chi k (fun _ _=>Logic.I) hU (smooth_cutoff_class hChi k)).
have hClass:norm_class_all_orders hNX hNY U (fun x=>chi x*:y).
  move=>k; exact:(norm_class_scalar_product (hScalar k)
    (@norm_class_constant R X Y NX NY hNX hNY U y k hU)).
have hZero x:~smooth_compact_carrier C x ->chi x*:y=0.
  move=>hx; have hc:=@real_function_zero_off_support R (real_norm_metric_space hNX) chi x hx.
  by rewrite hc scale0r.
have [f [hf hSupport]]:=@smooth_test_represents_with_support R X Y NX NY hNX hNY U E ev hE C
  (fun x=>chi x*:y) hClass hZero.
exists f; split; first by rewrite (hf a ha) hChiA scale1r.
move=>x hx; exact:(smooth_cutoff_support_in_domain hChi (hSupport x hx)).
Qed.
End TestEscapingPoint.
