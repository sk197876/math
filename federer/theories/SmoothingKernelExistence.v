(** Federer (1969), 4.1.2, p. 346: an
    actual nonnegative compact smooth kernel of integral
    one exists. The original smooth cutoff of 3.1.13
    gives a positive plateau; its square is normalized
    by its finite positive Lebesgue integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  NormRegularityOperations NormRegularityBilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactSupportFunctionUP SmoothCompactSet SmoothCompactCutoffUP SmoothCompactCutoffSealed NormCompactScalarSummability
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral PartialZeroExtensionLaws
  SummableRealFunctionUP SummableRealArithmetic SubsetIntegralArbitraryConstantLower SmoothingKernelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smoothing_kernel_exists]: the kernel chosen
    at the start of Federer 4.1.2, p. 346,
    satisfies every original condition in every Euclidean
    dimension, including dimension zero. *)
Theorem smoothing_kernel_exists (R:realType) n:
  exists phi:R_n R n->R,is_smoothing_kernel phi.
Proof.
pose X:=R_n R n.
pose hInner:=@euclidean_inner_productP R n.
pose NX:=inner_norm hInner.
pose hNX:=inner_norm_real_norm hInner.
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
pose W:= [set x:X|NX (x-0)<1].
have hZeroN:NX (0:X)=0:=real_seminorm_zero hNX.1.
have hZeroW:W 0.
  change (is_true (NX ((0:X)-0)<1)).
  by rewrite subrr hZeroN.
have hInterior x (hx:W x):norm_domain_interior NX W x.
  exact:(@norm_open_ball_domain_interior R X NX hNX 0 1 x hx).
pose A:=@smooth_compact_singleton R X NX hNX W 0 hZeroW.
pose chi:=@SmoothCompactCutoff.value R X NX hNX n (@coordinate_basis R n) (@coordinate_basisP R n) W A hInterior.
have hChi:=@SmoothCompactCutoff.laws R X NX hNX n (@coordinate_basis R n) (@coordinate_basisP R n) W A hInterior.
have [V [hV [hAV hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
have h0V:V 0:=hAV 0 (erefl 0).
pose C:=@Build_smooth_compact_set R X NX hNX (fun _=>True)
  (@real_function_support R (real_norm_metric_space hNX) chi)
  (fun _ _=>Logic.I) (smooth_cutoff_compact hChi).
pose g:=fun x=>chi x*chi x.
have hG:norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) g.
  move=>k; exact:(norm_class_scalar_product (smooth_cutoff_class hChi k) (smooth_cutoff_class hChi k)).
have hOff x:~smooth_compact_carrier C x ->g x=0.
  move=>hx; have h:=@real_function_zero_off_support R (real_norm_metric_space hNX) chi x hx.
  by rewrite /g h mul0r.
have [a hIntegral]:=@norm_compact_scalar_summable R X NX hNX mu hm
  (@euclidean_distribution_measure_borel R n) (@euclidean_distribution_measure_compact_finite R n)
  C g (norm_class_continuous (hG 0%N)) hOff.
have hG0 x:0<=g x by rewrite /g -expr2; exact:sqr_ge0.
have hG1 x:V x ->g x= 1.
  move=>hx; have hOneX:chi x= 1:=hOne x hx.
  by rewrite /g hOneX mul1r.
have hWhole:is_measure_subset_integral mu setT (real_total_integrand g) a%:E.
  apply:(@measure_integral_graph_equivalent R X mu (real_total_integrand g) _ a%:E _ hIntegral).
  move=>x y; symmetry; exact:partial_zero_extension_whole_graph.
have hLower:((1:R)%:E*mu V<=a%:E)%E.
  apply:(@subset_integral_arbitrary_positive_constant_lower R X mu hm V setT
    (real_total_integrand g) a%:E 1 (fun _ _=>Logic.I) ltr01 _ _ hWhole).
  - move=>x _; exists (g x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite lee_fin; exact:hG0.
  - move=>x y hx hy; move/real_total_integrand_graph:hy=> <-; by rewrite (hG1 x hx).
have hPositive:0<a.
  have hMassPos:=@euclidean_distribution_measure_open_positive R n V 0 hV h0V.
  rewrite mul1e in hLower.
  have h:=lt_le_trans hMassPos hLower.
  by rewrite lte_fin in h.
pose phi:=fun x=>a^-1*g x.
have hPhi:norm_class_all_orders hNX (@scalar_absolute_value_norm R) (fun _=>True) phi.
  move=>k; exact:(norm_class_scale a^-1 (hG k)).
have hSupport:@real_function_support R (real_norm_metric_space hNX) phi `<=` smooth_compact_carrier C.
  apply:(@real_function_support_in_closed_set R (real_norm_metric_space hNX) phi
    (smooth_compact_carrier C)).
  - exact:compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact C).
  - move=>x hx; by rewrite /phi (hOff x hx) mulr0.

have hCompact:@compact (real_norm_metric_space hNX) (@real_function_support R (real_norm_metric_space hNX) phi).
  apply:(@real_function_compact_support_in_closed_set R (real_norm_metric_space hNX) phi
    (smooth_compact_carrier C) (smooth_compact_is_compact C)).
  - exact:compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) (smooth_compact_is_compact C).
  - move=>x hx; by rewrite /phi (hOff x hx) mulr0.

exists phi; constructor; first exact hPhi.
- move=>x; have hInv:0<a^-1 by rewrite invr_gt0.
  exact:mulr_ge0 (ltW hInv) (hG0 x).
- exact hCompact.
- move=>x hx.
  have hRadius:W x:=smooth_cutoff_support_in_domain hChi (hSupport x hx).
  change (is_true (NX (x-0)<1)) in hRadius.
  change (is_true (NX x<1)).
  by rewrite subr0 in hRadius.
- have h:=@real_total_integral_scale R X mu hm g a a^-1 hIntegral.
  have hA:a!=0 by rewrite (gt_eqF hPositive).
  by rewrite mulVf // in h.
Qed.
