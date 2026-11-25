(** Federer (1969), 4.1.8, p. 362: the
    original point-current slice phi_delta_z is the
    actual pullback epsilon_z#phi. Pair the existing
    slice law with each original multivector and reuse
    the right-interior and degree-zero unit identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom GradedComponents RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingZero AlternatingDual AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces CurrentDirac CurrentDiracDensity CurrentCartesianDomain
  CurrentCartesianSliceUP CurrentCartesianSliceSealed CurrentCartesianSliceTestSealed CurrentCartesianSliceTestPairing
  CurrentCartesianVectorProduct CurrentZeroDegreeExteriorLaws CurrentCartesianPointInclusion
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianPointSlice.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variable z:X.
Hypothesis hz:A z.
Local Notation f := (@current_cartesian_point_inclusion R m n z).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n A B z hz y hy).
Local Notation hSmooth := (@current_cartesian_point_inclusion_smooth R m n B hB z).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).
Local Notation delta := (@dirac_current R h2 m A hA z).
Local Notation H := (@CartesianSlice.value R h2 m n 0%N j A B hA hB delta).
Local Notation G := (fun b hb=>@CartesianSliceTest.value R h2 m n A B hA hB 0%N j b hb).
Local Notation unit := (@current_scalar_multivector_unit R m).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB j).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB j).
Local Notation IC := (smooth_test_inclusion hEC).
Local Notation ta := (@current_test_value R h2 m A hA 0%N).
Local Notation tb := (@current_test_value R h2 n B hB j).
Local Notation tc := (@current_test_value R h2 (m+n) AB hAB j).
Local Notation pull := (@SmoothFormPullback.operator R h2 n (m+n) j B AB hB hAB f Image hSmooth).

(** Source for [current_cartesian_point_slice]: the
    original phi_delta_z(b) equals the actual pulled-back
    form epsilon_z#phi(b), precisely the reason given
    for the point-product identity in Federer 4.1.8,
    p. 362. Every original test phi is retained. *)
Theorem current_cartesian_point_slice phi b (hb:B b):
  tb (H phi) b=vb (pull (IC phi)) b.
Proof.
apply:pairing_ext=>eta.
have hSlice:=@CartesianSlice.laws R h2 m n 0%N j A B hA hB delta phi b hb eta.
rewrite dirac_current_evaluation in hSlice.
have hPair:=@current_cartesian_slice_test_pairing R h2 m n 0%N j A B hA hB
  b hb eta phi z hz unit.
rewrite current_scalar_multivector_unit_pairing in hPair.
have hF:@current_cartesian_vector_product R m n 0%N j unit eta=exterior_power_map Q j eta.
  by rewrite /current_cartesian_vector_product /current_scalar_multivector_unit
    exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_left scale1r.
rewrite hF in hPair.
have hPull:=@smooth_form_pullback_values R n (m+n) j B AB EC EB vc vb f pull
  (@SmoothFormPullback.laws R h2 n (m+n) j B AB hB hAB f Image hSmooth)
  (IC phi) b (@euclidean_last_injection_map R m n) hb
  (@current_cartesian_point_inclusion_differential R m n B hB z b hb).
rewrite hSlice hPair hPull A_m_dual_pairing;by [].
Qed.
End CurrentCartesianPointSlice.
