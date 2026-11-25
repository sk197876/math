(** Federer (1969), 4.1.18, p. 374: actual
    compact replacements compute the original averaged
    form. Agreement near the compact kernel-current
    support is enough; auxiliary cutoff choices are
    not part of the public definition.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology
  NormDifferentialUP NormRegularity NormClassZeroTopology NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap EuclideanBlockCoordinates ExteriorGrading AlternatingForms AlternatingZero AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentCartesianAffineSlice CurrentCartesianLocalCutoff CurrentCartesianSliceSealed
  CurrentCartesianSliceTestSealed CurrentCartesianSliceTestPairing
  CurrentKernelAverageUP CurrentKernelAverageSliceIntegral
  CurrentCompactKernelFormAverageUP CurrentTestNearSupportAgreement
  SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation MeasureIntegralUP
  MeasureIntegralUniqueness EuclideanLebesgueDimensions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactKernelFormAverageReplacement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation Z:=(R_n R (n+q)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+q))).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R q)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+q))).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation F:=(@current_smooth_space R h2 (n+q) AB hAB (0+j)).
Local Notation fv:=(@current_smooth_value R h2 (n+q) AB hAB (0+j)).
Local Notation DC:=(@current_test_space R h2 (n+q) AB hAB (0+j)).
Local Notation tv:=(@current_test_value R h2 (n+q) AB hAB (0+j)).
Local Notation E:=(@current_smooth_space R h2 q U hU j).
Local Notation ev:=(@current_smooth_value R h2 q U hU j).
Local Notation tvalue:=(@current_test_value R h2 q U hU j).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Variable K:smooth_compact_set hNX Full.
Hypothesis hOff:forall z,~smooth_compact_carrier K z->w z=0.
Variable A:Hom F E.
Hypothesis hA:@is_current_compact_kernel_form_average R h2 n q j U hU w A.
Local Notation Slice:=(@CartesianSlice.value R h2 n q 0%N j Full U hFull hU S).

(** Source for [current_compact_kernel_form_average_replacement]:
    one genuine compact test agreeing with the original
    smooth input along the whole kernel computes the
    averaged form at the given point, supporting
    Federer 4.1.18, p. 374. *)
Theorem current_compact_kernel_form_average_replacement
    (phi:F) (psi:DC) x (hx:U x):
  (forall z,smooth_compact_carrier K z->
    tv psi (euclidean_block_join (z,x))=fv phi (euclidean_block_join (z,x))) ->
  ev (A phi) x=tvalue (Slice psi) x.
Proof.
move=>hMatch;apply:pairing_ext=>eta.
have hIntegral:=@current_kernel_average_slice_integral R h2 n q j U hU
  w S hS psi x hx eta.
have hFunction:(fun z=>w z*
    pairing (@current_cartesian_vector_product R n q 0%N j unit eta)
      (tv psi (euclidean_block_join (z,x))))=
    @current_compact_kernel_form_integrand R h2 n q j U hU w phi x eta.
  apply:funext=>z;rewrite /current_compact_kernel_form_integrand.
  case:(pselect (smooth_compact_carrier K z))=>[hz|hz].
  - by rewrite (hMatch z hz).
  - by rewrite (@hOff z hz) !mul0r.
rewrite hFunction in hIntegral.
have hEqual:=measure_integral_unique (@hA phi x hx eta) hIntegral.
by injection hEqual.
Qed.

(** Source for [current_compact_kernel_form_average_near_support]:
    local agreement on the kernel-current support fixes
    the original averaged form. This is the support
    locality needed for the actual smoothing deformation
    action in Federer 4.1.18, p. 374. *)
Theorem current_compact_kernel_form_average_near_support
    (hSupport:@current_support R h2 n Full hFull 0%N S `<=` smooth_compact_carrier K)
    (phi psi:F) x (hx:U x) (O:set Z):
  @open (real_norm_metric_space hNZ) O ->
  (forall z,@current_support R h2 n Full hFull 0%N S z->
    O (euclidean_block_join (z,x))) ->
  (forall y,O y->fv phi y=fv psi y) ->ev (A phi) x=ev (A psi) x.
Proof.
move=>hO hSO hEqual.
have [Q [W [OQ [hW [hWx [hWU [hOQ [hKQ [hQDomain [hQ hStrip]]]]]]]]]]:=
  @current_cartesian_local_cutoff_strong R h2 n q (0+j)%N Full U hFull hU K x hx.
have hFirst:=@current_compact_kernel_form_average_replacement
  phi (Q phi) x hx (fun z hz=>@hStrip phi z x hz hWx).
have hSecond:=@current_compact_kernel_form_average_replacement
  psi (Q psi) x hx (fun z hz=>@hStrip psi z x hz hWx).
rewrite hFirst hSecond;apply:pairing_ext=>eta.
rewrite !(@CartesianSlice.laws R h2 n q 0%N j Full U hFull hU S _ x hx eta).
pose alpha:=fun theta=>@CartesianSliceTest.value R h2 n q Full U hFull hU
  0%N j x hx eta (Q theta).
pose J (z:X):Z:=euclidean_block_join (z,x).
pose V:set X:=J @^-1` (O `&` OQ).
have hJ:continuous (fun z:real_norm_metric_space hNX=>
    (J z:real_norm_metric_space hNZ)).
  move=>z;exact:(@norm_class_zero_continuous_at R X Z NX NZ hNX hNZ Full J z
    (norm_class_continuous (@current_cartesian_affine_slice_smooth R n q Full hFull x 0%N))
    Logic.I).
have hV:@open (real_norm_metric_space hNX) V.
  apply:open_comp (openI hO hOQ)=>z _;exact:hJ z.
apply:(@current_test_near_support_values_equal R h2 n 0%N Full hFull S
  (alpha phi) (alpha psi) V hV).
- move=>z hz;split;first exact:hSO z hz.
  exact:hKQ z (hSupport z hz).
- move=>z [hzO hzQ].
  apply:(can_inj (@zero_form_valueK R X R^o)).
  rewrite -!(@current_scalar_multivector_unit_pairing R n).
  rewrite !(@current_cartesian_slice_test_pairing R h2 n q 0%N j Full U hFull hU
    x hx eta _ z Logic.I unit).
  by rewrite (hQ phi (J z) hzQ) (hQ psi (J z) hzQ) (hEqual (J z) hzO).
Qed.
End CurrentCompactKernelFormAverageReplacement.
