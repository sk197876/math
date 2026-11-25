(** Federer (1969), 4.1.18, p. 374: local
    actual smooth Cartesian slices realise the original
    compact-kernel form integral. The cutoffs are only
    existence witnesses; the whole kernel is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap EuclideanBlockCoordinates ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentCartesianDomain CurrentCartesianVectorProduct
  CurrentCartesianSliceSealed CurrentCartesianLocalCutoff SmoothCompactSet
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CurrentKernelAverageUP CurrentKernelAverageSliceIntegral
  CurrentCompactKernelFormAverageUP MeasureIntegralUP
  EuclideanLebesgueDimensions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactKernelFormAverageLocal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R q)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation F:=(@current_smooth_space R h2 (n+q) AB hAB (0+j)).
Local Notation fv:=(@current_smooth_value R h2 (n+q) AB hAB (0+j)).
Local Notation E:=(@current_smooth_space R h2 q U hU j).
Local Notation ev:=(@current_smooth_value R h2 q U hU j).
Local Notation hE:=(@current_smooth_space_laws R h2 q U hU j).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Variable K:smooth_compact_set hNX Full.
Hypothesis hOff:forall z,~smooth_compact_carrier K z->w z=0.
Local Notation Integrand:=(@current_compact_kernel_form_integrand R h2 n q j U hU w).
Local Notation Slice:=(@CartesianSlice.value R h2 n q 0%N j Full U hFull hU S).
Local Notation Inc:=(smooth_test_inclusion hE).

(** Source for [current_compact_kernel_form_average_local]:
    a single actual linear smooth operator realises
    every original kernel integral near a source point,
    supporting Federer 4.1.18, p. 374. Every
    original smooth input is allowed, without compact
    support or separability assumptions. *)
Theorem current_compact_kernel_form_average_local x (hx:U x):
  exists (L:Hom F E) (W:set Y),
    @open (real_norm_metric_space hNY) W /\W x /\W `<=` U /\
    forall phi y,W y->forall eta:exterior_power Y j,
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (Integrand phi y eta))
        (pairing eta (ev (L phi) y))%:E.
Proof.
have [Q [W [hW [hWx [hWU hQ]]]]]:=
  @current_cartesian_local_cutoff R h2 n q (0+j)%N Full U hFull hU K x hx.
pose L:=hom_comp Inc (hom_comp Slice Q).
exists L,W;split=>//;split=>//;split=>// phi y hy eta.
have hIntegral:=@current_kernel_average_slice_integral R h2 n q j U hU
  w S hS (Q phi) y (hWU y hy) eta.
change (is_measure_integral (@euclidean_lebesgue_measure R n)
  (real_total_integrand (fun z=>w z*
    pairing (@current_cartesian_vector_product R n q 0%N j
      (@current_scalar_multivector_unit R n) eta)
      (@current_test_value R h2 (n+q) AB hAB (0+j)
        (Q phi) (euclidean_block_join (z,y)))))
  (pairing eta (ev (L phi) y))%:E) in hIntegral.
have hFunction:(fun z=>w z*
    pairing (@current_cartesian_vector_product R n q 0%N j
      (@current_scalar_multivector_unit R n) eta)
      (@current_test_value R h2 (n+q) AB hAB (0+j)
        (Q phi) (euclidean_block_join (z,y))))=Integrand phi y eta.
  apply:funext=>z;rewrite /current_compact_kernel_form_integrand.
  case:(pselect (smooth_compact_carrier K z))=>[hz|hz].
  - by rewrite (@hQ phi z y hz hy).
  - by rewrite (@hOff z hz) !mul0r.
by rewrite -hFunction.
Qed.
End CurrentCompactKernelFormAverageLocal.
