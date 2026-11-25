(** Federer (1969), 4.1.18, p. 375: compact
    parameter averaging commutes with the spatial
    exterior differential. For actual tests, derive
    this from the original zero-first-factor Cartesian
    boundary identity of 4.1.8, rather than proving
    a new differentiation-under-the-integral theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces CurrentBoundary
  CurrentDegreeTransportIdentity CurrentTestExteriorDerivative
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductAction
  CurrentCartesianSliceSealed CurrentCartesianBoundarySecondZero
  PointMultivectorCurrentUP PointMultivectorCurrentSealed
  SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianZeroSliceExteriorDerivative.
Variable R:realType.
Hypothesis h2:(1+1:R)!= 0.
Variables m n j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall x,A x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB:forall x,B x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B x.
Local Notation AB:=(@euclidean_cartesian_set R m n A B).
Local Notation hAB:=(@current_cartesian_domain_open R m n A B hA hB).
Variable S:@current_space R h2 m A hA 0%N.
Local Notation Slice:=(fun d=>@CartesianSlice.value R h2 m n 0%N d A B hA hB S).

(** Source for [current_cartesian_zero_slice_exterior_derivative]:
    d(phi_S)=(d phi)_S for every actual joint
    test and original zero-current S, by the
    original product boundary law. This supports
    the form assertion of 4.1.18, p. 375. *)
Theorem current_cartesian_zero_slice_exterior_derivative
    (phi:@current_test_space R h2 (m+n)%N AB hAB j):
  @current_test_exterior_derivative R h2 n j B hB (Slice j phi)=
  Slice j.+1 (@current_test_exterior_derivative R h2 (m+n)%N j AB hAB phi).
Proof.
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 n B hB j.+1))=>x hx.
apply:pairing_ext=>eta.
pose T:=@PointMultivectorCurrent.value R h2 n j.+1 B hB x hx eta.
have hBoundary:=@current_cartesian_boundary_second_zero R h2 m n A B hA hB j S T.
rewrite current_degree_transport_identity in hBoundary.
have hValue:=congr1 (fun C:@current_space R h2 (m+n)%N AB hAB j=>
  @current_value R h2 (m+n)%N AB hAB j C phi) hBoundary.
rewrite current_boundary_evaluation !current_cartesian_product_action
  current_boundary_evaluation in hValue.
rewrite !(@PointMultivectorCurrent.laws R h2 n j.+1 B hB x hx eta) in hValue.
exact:esym hValue.
Qed.
End CurrentCartesianZeroSliceExteriorDerivative.
