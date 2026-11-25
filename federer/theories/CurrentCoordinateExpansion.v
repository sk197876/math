(** Federer (1969), 4.1.7, p. 356: the
    original current is reconstructed from its
    scalar coordinate currents and constant coordinate
    multivectors. The proof transposes the actual
    compact-test expansion; it uses no representation
    by a measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FiniteExteriorPowers Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorIndices FiniteCoordinates
  CovectorProducts EuclideanCoordinateForms CurrentSpaces CurrentVectorSpaces CurrentConstantFields
  CurrentDegreeTransport CurrentDegreeTransportInverse CurrentEvaluation CurrentPointEvaluation
  CurrentContraction CurrentVectorProduct CurrentTestFormProduct CurrentTestVectorInterior
  CurrentTestCoordinateExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCoordinateExpansion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun d=>@current_space R h2 n U hU d).
Local Notation DT := (fun d=>@current_test_space R h2 n U hU d).
Local Notation cf := (@current_constant_form R h2 n U hU).
Local Notation cv := (@current_constant_vector R h2 n U hU).
Local Notation el := (fun lambda:Lambda n m=>e_lambda (@coordinate_basis R n) (val lambda)).
Local Notation wl := (@omega_lambda R h2 X n (@euclidean_coordinate_form R n) m).
Local Notation P := (@current_contraction R h2 n m 0 U hU).
Local Notation V := (@current_vector_product R h2 n m 0 U hU).
Local Notation Pt := (@current_test_form_product R h2 n m 0 U hU).
Local Notation It := (@current_test_vector_interior R h2 n m 0 U hU).
Local Notation Tr := (@current_degree_transport R h2 n U hU (m+0) m (addn0 m)).
Local Notation Trt := (@current_test_degree_transport R h2 n U hU m (m+0) (esym (addn0 m))).

(** Source for [current_coordinate_expansion]: the
    original identity T=sum_lambda (T contracted
    DX_lambda) wedge e_lambda, Federer 4.1.7,
    p. 356, fourth displayed formula.
    Equal degree m+0=m is explicit; all
    degrees, including m>n, are retained. *)
Theorem current_coordinate_expansion (T:C (m+0)):
  Tr T=\sum_(lambda:Lambda n m) Tr (V (cv m (el lambda)) (P (cf m (wl lambda)) T)).
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>psi.
have hTests:Trt psi=\sum_(lambda:Lambda n m)
    Pt (cf m (wl lambda)) (It (cv m (el lambda)) (Trt psi)).
  apply:(can_inj (@current_test_degree_transport_inverse R h2 n U hU
    (m+0) m (addn0 m))).
  rewrite linear_sum.
  exact:current_test_coordinate_expansion.
rewrite current_degree_transport_evaluation current_value_finite_sum.
under eq_bigr do rewrite current_degree_transport_evaluation
  current_vector_product_evaluation current_contraction_evaluation.
have hAction:=congr1 (@current_value R h2 n U hU (m+0) T) hTests.
rewrite linear_sum in hAction.
exact:hAction.
Qed.
End CurrentCoordinateExpansion.
