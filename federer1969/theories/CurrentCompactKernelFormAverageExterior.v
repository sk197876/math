(** Federer (1969), 4.1.18, p. 375: the
    original compact-kernel form average commutes with
    exterior differentiation on the spatial factor.
    Local genuine tests reduce this to the old
    zero-factor Cartesian boundary law, preserving
    arbitrary original smooth forms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import EuclideanBlockCoordinates Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap AlternatingForms CurrentSpaces CurrentCartesianDomain
  CurrentCartesianLocalCutoff CurrentCartesianSliceSealed CurrentCartesianZeroSliceExteriorDerivative
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  SmoothCurrentExteriorDerivative CurrentTestExteriorDerivative CurrentTestExteriorAgreement
  CurrentKernelAverageUP CurrentCompactKernelFormAverageUP
  CurrentCompactKernelFormAverageReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCompactKernelFormAverageExterior.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation Z:=(R_n R (n+q)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+q)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R q)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation F:=(fun d=>@current_smooth_space R h2 (n+q)%N AB hAB d).
Local Notation fv:=(fun d=>@current_smooth_value R h2 (n+q)%N AB hAB d).
Local Notation E:=(fun d=>@current_smooth_space R h2 q U hU d).
Local Notation ev:=(fun d=>@current_smooth_value R h2 q U hU d).
Local Notation tv:=(fun d=>@current_test_value R h2 q U hU d).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Variable K:smooth_compact_set hNX Full.
Hypothesis hOff:forall z,~smooth_compact_carrier K z->w z= 0.
Variables (A:Hom (F j) (E j)) (ANext:Hom (F j.+1) (E j.+1)).
Hypothesis hA:@is_current_compact_kernel_form_average R h2 n q j U hU w A.
Hypothesis hANext:@is_current_compact_kernel_form_average R h2 n q j.+1 U hU w ANext.

(** Source for [current_compact_kernel_form_average_exterior]:
    d(A phi)= A(d phi), the spatial exterior
    differential commutation needed to average the
    original form homotopy, Federer 4.1.18,
    p. 375. No differentiability or separability
    premise is added to the kernel-current laws. *)
Theorem current_compact_kernel_form_average_exterior (phi:F j):
  @smooth_current_exterior_derivative R h2 q j U hU (A phi)=
  ANext (@smooth_current_exterior_derivative R h2 (n+q)%N j AB hAB phi).
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 q U hU j.+1))=>x hx.
have[Q [W [O [hW [hxW [hWU [hO [hKO [hOAB [hQ hStrip]]]]]]]]]]:=
  @current_cartesian_local_cutoff_strong R h2 n q j Full U hFull hU K x hx.
pose psi:=Q phi.
pose Slice:=(fun d=>@CartesianSlice.value R h2 n q 0%N d Full U hFull hU S).
have hAgreement y (hy:W y):tv j (Slice j psi) y= ev j (A phi) y.
  apply:esym.
  exact:(@current_compact_kernel_form_average_replacement R h2 n q j U hU
    w S hS K hOff A hA phi psi y (hWU y hy)
    (fun z hz=>hStrip phi z y hz hy)).
have hDerivative:=@current_test_exterior_local_agreement R h2 q j U hU
  (Slice j psi) (A phi) W hW hWU hAgreement x hxW.
have hJointDerivative:=@current_test_exterior_local_agreement R h2 (n+q)%N j AB hAB
  psi phi O hO hOAB (fun y hy=>hQ phi y hy).
have hNext:=@current_compact_kernel_form_average_replacement R h2 n q j.+1 U hU
  w S hS K hOff ANext hANext
  (@smooth_current_exterior_derivative R h2 (n+q)%N j AB hAB phi)
  (@current_test_exterior_derivative R h2 (n+q)%N j AB hAB psi) x hx
  (fun z hz=>hJointDerivative (euclidean_block_join (z,x)) (hKO z hz)).
rewrite -hDerivative hNext -current_cartesian_zero_slice_exterior_derivative.
reflexivity.
Qed.
End CurrentCompactKernelFormAverageExterior.
