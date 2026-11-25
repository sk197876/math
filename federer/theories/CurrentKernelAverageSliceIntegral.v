(** Federer (1969), 4.1.18, p. 374: every
    compact-kernel form average is the actual original
    Cartesian slice. Its pointwise scalar integral follows
    directly from the earlier slice pairing and the
    kernel-current density law.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap EuclideanBlockCoordinates AlternatingZero ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentCartesianDomain
  CurrentCartesianVectorProduct CurrentCartesianSliceSealed
  CurrentCartesianSliceTestSealed CurrentCartesianSliceTestPairing
  CurrentKernelAverageUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  EuclideanLebesgueDimensions SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentKernelAverageSliceIntegral.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R q).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Variable U:set Y.
Hypothesis hU:forall x,U x->norm_domain_interior NY U x.
Local Notation AB:=(@euclidean_cartesian_set R n q Full U).
Local Notation hAB:=(@current_cartesian_domain_open R n q Full U hFull hU).
Local Notation DC:=(@current_test_space R h2 (n+q) AB hAB (0+j)).
Local Notation value:=(@current_test_value R h2 (n+q) AB hAB (0+j)).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variable w:X->R.
Variable S:@current_space R h2 n Full hFull 0%N.
Hypothesis hS:@is_current_kernel_average R h2 n w S.
Local Notation Slice:=(@CartesianSlice.value R h2 n q 0%N j Full U hFull hU S).

(** Source for [current_kernel_average_slice_integral]:
    literal compact parameter integration of the original
    form coefficients, supporting the smoothing transgression
    in Federer 4.1.18, p. 374. The result
    is an actual smooth compact test before it is
    evaluated by another arbitrary current. *)
Theorem current_kernel_average_slice_integral (phi:DC) x (hx:U x)
    (eta:exterior_power Y j):
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand (fun z=>w z*
      pairing (@current_cartesian_vector_product R n q 0%N j unit eta)
        (value phi (euclidean_block_join (z,x)))))
    (pairing eta (@current_test_value R h2 q U hU j (Slice phi) x))%:E.
Proof.
pose psi:=@CartesianSliceTest.value R h2 n q Full U hFull hU
  0%N j x hx eta phi.
have hIntegral:=hS psi.
have hPoint z:
    zero_form_value (@current_test_value R h2 n Full hFull 0%N psi z)=
    pairing (@current_cartesian_vector_product R n q 0%N j unit eta)
      (value phi (euclidean_block_join (z,x))).
  rewrite -(@current_scalar_multivector_unit_pairing R n
    (@current_test_value R h2 n Full hFull 0%N psi z)).
  exact:(@current_cartesian_slice_test_pairing R h2 n q 0%N j
    Full U hFull hU x hx eta phi z Logic.I unit).
have hFunction:(fun z=>w z*zero_form_value
    (@current_test_value R h2 n Full hFull 0%N psi z))=
    (fun z=>w z*
      pairing (@current_cartesian_vector_product R n q 0%N j unit eta)
        (value phi (euclidean_block_join (z,x)))).
  by apply:funext=>z;rewrite hPoint.
rewrite hFunction in hIntegral.
rewrite (@CartesianSlice.laws R h2 n q 0%N j Full U hFull hU
  S phi x hx eta).
exact:hIntegral.
Qed.
End CurrentKernelAverageSliceIntegral.
