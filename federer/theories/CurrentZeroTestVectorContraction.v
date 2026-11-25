(** Federer (1969), 4.1.7, p. 356: the
    actual test identity behind contraction of
    a zero-current vector product. It is
    precisely the earlier characteristic left-interior
    pairing, applied pointwise to original tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms
  AlternatingZero AlternatingSum AlternatingPairing ExteriorHomogeneousProducts ComassWedgeSymmetry
  CurrentSpaces CurrentVectorSpaces CurrentDegreeTransport CurrentTestFormProduct CurrentTestVectorInterior
  CurrentInteriorPairing CurrentVectorFormInterior CurrentVectorContraction SmoothCurrentVectorContraction
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentZeroTestVectorContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation X := (R_n R n).
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation DT := (fun m=>@current_test_space R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation ev := (fun m=>@current_test_value R h2 n U hU m).
Local Notation I := (fun m=>@current_test_vector_interior R h2 n m 0 U hU).
Local Notation P := (@current_test_form_product R h2 n k p U hU).
Local Notation L := (@smooth_current_vector_contraction R h2 n k p U hU).
Local Notation Tr := (fun m=>@current_test_degree_transport R h2 n U hU m (m+0) (esym (addn0 m))).

(** Source for [current_zero_test_vector_contraction]:
    the two original zero-form tests agree,
    supporting the seventh displayed identity in
    Federer 4.1.7, p. 356. This
    uses the actual current multipliers and
    equal-degree transports throughout. *)
Theorem current_zero_test_vector_contraction (xi:V (k+p)) (phi:E k) (psi:DT p):
  I (k+p) xi (Tr (k+p) (P phi psi))=I p (L xi phi) (Tr p psi).
Proof.
apply:(smooth_test_values_extensional (hE 0))=>x hx.
change (@current_test_value R h2 n U hU 0%N
    (I (k+p) xi (Tr (k+p) (P phi psi))) x=
  @current_test_value R h2 n U hU 0%N (I p (L xi phi) (Tr p psi)) x).
apply:(can_inj (@zero_form_valueK R X R^o)).
rewrite (@current_test_vector_interior_values R h2 n (k+p) 0 U hU xi
  (Tr (k+p) (P phi psi)) x hx).
rewrite (@current_test_vector_interior_values R h2 n p 0 U hU (L xi phi) (Tr p psi) x hx).
rewrite !current_vector_interior_scalar_value.
rewrite (@current_test_degree_transport_values R h2 n U hU (k+p) ((k+p)+0)
  (esym (addn0 (k+p))) (P phi psi) x).
rewrite (@current_test_degree_transport_values R h2 n U hU p (p+0)
  (esym (addn0 p)) psi x).
rewrite !form_reindex_include.
rewrite (@current_test_form_product_values R h2 n k p U hU phi psi x hx).
rewrite (@smooth_current_vector_contraction_values R h2 n k p U hU xi phi x hx).
symmetry;exact:current_vector_contraction_pairing.
Qed.
End CurrentZeroTestVectorContraction.
