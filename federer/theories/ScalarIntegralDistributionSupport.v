(** Federer (1969), 4.1.1, p. 345: a
    distribution need not have compact support. For a
    measure positive on nonempty open sets, scalar
    integration has full support. The proof uses the
    original compact smooth cutoffs of 3.1.13. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology LinearBasis
  NormRegularity NormRegularityBilinear CompactSupportFunctionUP SmoothCompactSet SmoothCompactCutoffUP SmoothCompactCutoffSealed
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestCompactRepresentation
  FunctionalSupportUP NormOpenTopology PartialFunctionBasic SummableRealFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence PartialZeroExtensionLaws MeasureSubsetIntegral SubsetIntegralArbitraryConstantLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarIntegralSupport.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hPositive:forall (A:set X) x,@open (real_norm_metric_space hNX) A ->A x ->(0<mu A)%E.
Variable E:lmodType R.
Variable ev:E->X->R^o.
Hypothesis hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X R^o NX hNX (fun _=>True) DT value).
Variable T:Hom DT R^o.
Hypothesis hIntegral:forall f:DT,is_measure_integral mu (real_total_integrand (value f)) (T f)%:E.

(** Source for [scalar_integral_distribution_full_support]: the
    integration distribution has support equal to its whole
    source, giving the noncompact-support assertion of
    Federer 4.1.1, p. 345, for Euclidean Lebesgue measure. *)
Theorem scalar_integral_distribution_full_support:
  @smooth_functional_support R X R^o NX hNX (fun _=>True) DT value T=setT.
Proof.
apply:funext=>a; apply:propext; split=>// _; split=>//.
move=>[W [[hW hAnn] ha]].
have hInterior x (hx:W x):norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:open_nbhs_nbhs (conj hW hx).
pose A:=@smooth_compact_singleton R X NX hNX W a ha.
pose chi:=@SmoothCompactCutoff.value R X NX hNX d b hb W A hInterior.
have hChi:=@SmoothCompactCutoff.laws R X NX hNX d b hb W A hInterior.
have [V [hV [hAV hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
have haV:V a:=hAV a (erefl a).
pose C:=@Build_smooth_compact_set R X NX hNX (fun _=>True)
  (@real_function_support R (real_norm_metric_space hNX) chi)
  (fun _ _=>Logic.I) (smooth_cutoff_compact hChi).
pose g:=fun x=>chi x*chi x.
have hClass:norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) g.
  move=>k; exact:(norm_class_scalar_product (smooth_cutoff_class hChi k) (smooth_cutoff_class hChi k)).
have hZero x:~smooth_compact_carrier C x ->g x=0.
  move=>hx; have h:=@real_function_zero_off_support R (real_norm_metric_space hNX) chi x hx.
  by rewrite /g h mul0r.
have [f [hValue hSupport]]:=@smooth_test_represents_with_support R X R^o NX (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) (fun _=>True) E ev hE C g hClass hZero.
have hFW:support f `<=` W.
  move=>x hx; exact:(smooth_cutoff_support_in_domain hChi (hSupport x hx)).
have hTf:T f=0:=hAnn f hFW.
have hNonnegative x:0<=value f x.
  rewrite (hValue x Logic.I) /g -expr2; exact:sqr_ge0.
have hPlateau x:V x ->value f x= 1.
  move=>hx; have hOneX:chi x= 1:=hOne x hx.
  by rewrite (hValue x Logic.I) /g hOneX mul1r.
have hSubset:is_measure_subset_integral mu setT (real_total_integrand (value f)) (T f)%:E.
  apply:(@measure_integral_graph_equivalent R X mu (real_total_integrand (value f)) _ (T f)%:E _ (hIntegral f)).
  move=>x y; symmetry; exact:partial_zero_extension_whole_graph.
have hBound:((1:R)%:E*mu V<=(T f)%:E)%E.
  apply:(@subset_integral_arbitrary_positive_constant_lower R X mu hm V setT
    (real_total_integrand (value f)) (T f)%:E 1 (fun _ _=>Logic.I) ltr01 _ _ hSubset).
  - move=>x _; exists (value f x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite lee_fin; exact:hNonnegative.
  - move=>x y hx hy; move/real_total_integrand_graph:hy=> <-.
    by rewrite (hPlateau x hx).
have hPos:=@hPositive V a hV haV.
rewrite mul1e hTf in hBound.
by move:hPos; rewrite ltNge hBound.
Qed.
End ScalarIntegralSupport.
