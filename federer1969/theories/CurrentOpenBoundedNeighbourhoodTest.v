(** Federer (1969), 4.1.24, p. 381: bounded
    original scalar tests isolate the finite atoms
    of integral polyhedral zero-currents. This original-open
    adapter uses the preceding compact cutoff, unit-range
    replacement and scalar test realization. No extension
    of a noncompact test is evaluated. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates AlternatingZero
  CurrentSpaces CurrentZeroCovectorMaps CurrentSupportGeometry SmoothCompactSet
  SmoothCompactCutoffUP SmoothCompactCutoffSealed SmoothCutoffUnitRange
  CompactSupportFunctionUP CurrentScalarCompactFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_open_bounded_neighbourhood_test_exists]:
    the finite-atom tests needed for R_0=integral
    polyhedral P_0 in 4.1.24, p. 381.
    Values remain in [0,1], the test is one
    on K and its full support lies in W. *)
Theorem current_open_bounded_neighbourhood_test_exists
    (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (W:set (R_n R n)):
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) W->
  W `<=` U->smooth_compact_carrier K `<=` W->
  exists gamma:@current_test_space R h2 n U hU 0%N,
    @current_test_support R h2 n 0%N U hU gamma `<=` W /\
    (forall x,U x->0<=zero_form_value (@current_test_value R h2 n U hU 0%N gamma x)<=1) /\
    forall x,smooth_compact_carrier K x->
      @current_test_value R h2 n U hU 0%N gamma x=@zero_form R (R_n R n) R^o 1.
Proof.
move=>hW hWU hKW.
pose X:=R_n R n;pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hAbs:=@scalar_absolute_value_norm R.
have hWi:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:open_nbhs_nbhs (conj hW hx).
pose KW:=@Build_smooth_compact_set R X NX hNX W (smooth_compact_carrier K)
  hKW (smooth_compact_is_compact K).
pose chi:=@SmoothCompactCutoff.value R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) W KW hWi.
pose hChi:=@SmoothCompactCutoff.laws R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) W KW hWi.
have[psi [hPsi [hRange hSupport]]]:=smooth_cutoff_unit_range_exists hChi.
pose C:=@Build_smooth_compact_set R X NX hNX U
  (@real_function_support R (real_norm_metric_space hNX) psi)
  (fun x hx=>@hWU x (smooth_cutoff_support_in_domain hPsi hx))
  (smooth_cutoff_compact hPsi).
have hSmooth:norm_class_all_orders hNX hAbs U psi.
  move=>k;exact:(@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|)
    hNX hAbs (fun _=>True) U psi k (fun _ _=>Logic.I) hU (smooth_cutoff_class hPsi k)).
have[gamma [hValue hGammaSupport]]:=@current_scalar_compact_function_exists
  R h2 n U hU C psi hSmooth
  (fun x hx=>@real_function_zero_off_support R (real_norm_metric_space hNX) psi x hx).
exists gamma;split.
- exact:subset_trans hGammaSupport (smooth_cutoff_support_in_domain hPsi).
- split.
  + move=>x hx;by rewrite (@hValue x hx) zero_formK.
  + have[V [hV [hKV hOne]]]:=smooth_cutoff_neighbourhood_plateau hPsi.
    move=>x hx;rewrite (@hValue x (smooth_compact_in_domain K x hx))
      (@hOne x (@hKV x hx));by [].
Qed.
