(** Federer (1969), 4.1.18, p. 374: the
    scalar integral/current interchange follows from the
    preceding all-test Cartesian action and signed swap.
    The second factor remains an arbitrary current.
    No current-valued integral is assumed.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanCartesianMap AlternatingZero AlternatingForms ExteriorGrading AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentDegreeTransport
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductAction
  CurrentCartesianProductSwap CurrentCartesianSwapDomain CurrentCartesianSwapPushforward
  CurrentCartesianSwapTests
  CurrentCartesianSliceSealed CurrentCartesianSliceTestSealed
  SmoothFormPullbackSealed SmoothTestSpaces SmoothTestEvaluation
  EuclideanCartesianSwapLinear EuclideanLebesgueDimensions
  CurrentKernelAverageUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentKernelAverageFubini.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation DC:=(fun k=>@current_test_space R h2 (n+n) AB hAB k).
Local Notation EC:=(fun k=>@current_smooth_space R h2 (n+n) AB hAB k).
Local Notation evC:=(fun k=>@current_smooth_value R h2 (n+n) AB hAB k).
Local Notation tvC:=(fun k=>@current_test_value R h2 (n+n) AB hAB k).
Local Notation hEC:=(fun k=>@current_smooth_space_laws R h2 (n+n) AB hAB k).
Local Notation swap:=(@euclidean_cartesian_swap_map R n n).
Local Notation hImage:=(fun z hz=>@current_cartesian_swap_image R n n Full Full z hz).
Local Notation hSmooth:=(@euclidean_cartesian_swap_smooth R n n AB hAB).
Local Notation pull:=(fun k=>@SmoothFormPullback.operator R h2 (n+n) (n+n) k
  AB AB hAB hAB swap hImage hSmooth).
Local Notation Product:=(fun i k=>@CartesianCurrentProduct.value R h2 n n i k
  Full Full hFull hFull).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Variable T:@current_space R h2 n Full hFull j.

(** Source for [current_kernel_average_cartesian_action]:
    the compact-parameter integral/T interchange in the
    first display of Federer 4.1.18, p. 374.
    The auxiliary test psi is an actual swapped pullback;
    its existence is a separate compact-support adapter.
    The original current T needs no representation or
    finite mass. *)
Theorem current_kernel_average_cartesian_action
    (phi:DC (0+j)) (psi:DC (j+0)):
  (forall z,AB z ->tvC (j+0) psi z=
    evC (j+0)
      (pull (j+0) (smooth_test_inclusion (hEC (j+0))
        (@current_test_degree_transport R h2 (n+n) AB hAB
          (0+j) (j+0) (esym (addnC j 0)) phi))) z) ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>
      w z*@current_value R h2 n Full hFull j T
        (@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
          z Logic.I (@current_scalar_multivector_unit R n) psi)))
    (@current_value R h2 (n+n) AB hAB (0+j) (Product 0%N j S T) phi)%:E.
Proof.
move=>hPoint.
pose Reverse:=Product j 0%N T S.
pose beta:=@CartesianSlice.value R h2 n n j 0%N Full Full hFull hFull T psi.
have hIntegral:=hS beta.
have hIntegrand z:
    zero_form_value (@current_test_value R h2 n Full hFull 0%N beta z)=
    @current_value R h2 n Full hFull j T
      (@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
        z Logic.I (@current_scalar_multivector_unit R n) psi).
  rewrite -(@current_scalar_multivector_unit_pairing R n
    (@current_test_value R h2 n Full hFull 0%N beta z)).
  exact:(@CartesianSlice.laws R h2 n n j 0%N Full Full hFull hFull
    T psi z Logic.I (@current_scalar_multivector_unit R n)).
have hFunction:(fun z=>w z*zero_form_value
    (@current_test_value R h2 n Full hFull 0%N beta z))=
    (fun z=>w z*@current_value R h2 n Full hFull j T
      (@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
        z Logic.I (@current_scalar_multivector_unit R n) psi)).
  by apply:funext=>z;rewrite hIntegrand.
rewrite hFunction in hIntegral.
have hSwap:=@current_cartesian_product_swap R h2 n n Full Full hFull hFull
  j 0%N T S.
rewrite muln0 expr0 scale1r in hSwap.
have hValue:=congr1
  (fun Q=>@current_value R h2 (n+n) AB hAB (0+j) Q phi) hSwap.
rewrite current_degree_transport_evaluation in hValue.
have hAction:=@current_cartesian_swap_action R h2 n n Full Full hFull hFull
  (j+0)%N Reverse
  (@current_test_degree_transport R h2 (n+n) AB hAB
    (0+j) (j+0) (esym (addnC j 0)) phi) psi hPoint.
rewrite hAction current_cartesian_product_action in hValue.
rewrite current_cartesian_product_action -hValue.
rewrite current_cartesian_product_action;exact:hIntegral.
Qed.

(** Source for [current_kernel_average_cartesian_integral]:
    the preceding integral identity with an internally
    supplied genuine swapped test, supporting the first
    display of Federer 4.1.18, p. 374. The
    final statement has no extra test-replacement premise. *)
Theorem current_kernel_average_cartesian_integral (phi:DC (0+j)):
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>
      w z*@current_value R h2 n Full hFull j T
        (@CartesianSliceTest.value R h2 n n Full Full hFull hFull j 0%N
          z Logic.I (@current_scalar_multivector_unit R n)
          (@current_cartesian_swap_tests R h2 n n (j+0)%N Full Full hFull hFull
            (@current_test_degree_transport R h2 (n+n) AB hAB
              (0+j) (j+0) (esym (addnC j 0)) phi)))))
    (@current_value R h2 (n+n) AB hAB (0+j) (Product 0%N j S T) phi)%:E.
Proof.
apply:current_kernel_average_cartesian_action=>z _.
exact:(congr1 (fun e=>evC (j+0) e z)
  (@current_cartesian_swap_tests_inclusion R h2 n n (j+0)%N Full Full hFull hFull
    (@current_test_degree_transport R h2 (n+n) AB hAB
      (0+j) (j+0) (esym (addnC j 0)) phi))).
Qed.
End CurrentKernelAverageFubini.
