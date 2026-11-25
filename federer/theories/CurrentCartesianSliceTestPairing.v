(** Federer (1969), 4.1.8, p. 360: the
    original slice test is characterized by pairing the
    full test with the two included exterior vectors.
    Reuse the actual right-interior characteristic law
    rather than reconstructing alternating-form coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GradedComponents BoundedHom HomogeneousHom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts
  AlternatingForms AlternatingDual AlternatingPairing AlternatingSum ComassWedgeSymmetry
  CurrentSpaces CurrentCartesianDomain CurrentVectorFormInterior CurrentInteriorPairing
  CurrentCartesianSliceTestUP CurrentCartesianSliceTestSealed CurrentCartesianVectorProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceTestPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation G := (fun b hb=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).
Local Notation F := (@current_cartesian_vector_product R m n i j).
Local Notation va := (@current_test_value R h2 m A hA i).
Local Notation vc := (@current_test_value R h2 (m+n) AB hAB (i+j)).
Local Notation P := (hom_as_linear (@euclidean_first_injection_map R m n)).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).

(** Source for [current_cartesian_slice_test_pairing]: the
    original first-variable test pairs xi with exactly
    the full-test value on Lambda_i P xi wedge
    Lambda_j Q eta, supporting the defining slice
    display in Federer 4.1.8, p. 360. *)
Theorem current_cartesian_slice_test_pairing b (hb:B b)
    (eta:exterior_power Y j) phi a (ha:A a) (xi:exterior_power X i):
  pairing xi (va (G b hb eta phi) a)=
    pairing (F xi eta) (vc phi (euclidean_block_join (a,b))).
Proof.
rewrite ((@CartesianSliceTest.laws R h2 m n A B hA hB i j b hb).2 eta phi a ha)
  A_m_dual_pairing.
change (form_include (current_vector_form_interior (exterior_power_map Q j eta)
    (form_reindex (addnC i j) (vc phi (euclidean_block_join (a,b)))))
    (component_val (exterior_power_map P i xi))=
  pairing (F xi eta) (vc phi (euclidean_block_join (a,b)))).
rewrite current_vector_form_interior_include form_reindex_include.
by [].
Qed.
End CurrentCartesianSliceTestPairing.
