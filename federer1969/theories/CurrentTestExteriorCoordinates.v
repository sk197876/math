(** Federer (1969), 4.1.7, p. 356: the
    original coordinate formula for d on actual
    compact tests, before transposition to currents. *)
From mathcomp Require Import functions all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms
  AlternatingForms Alternating AlternatingSum AlternatingProduct ScalarCoefficients
  ExteriorHomogeneousProducts ComassWedgeSymmetry CurrentSpaces CurrentDegreeTransport CurrentConstantFields
  SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSpaceLaws CurrentDirectionalDerivative
  CurrentTestDirectionalInclusion CurrentTestFormProduct CurrentTestExteriorDerivative
  SmoothCurrentExteriorDerivative SmoothCurrentExteriorCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestExteriorCoordinates.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hE := (fun k=>@current_smooth_space_laws R h2 n U hU k).
Local Notation value := (fun k=>smooth_test_values_hom (hE k)).
Local Notation ev := (fun k=>@current_test_value R h2 n U hU k).
Local Notation sv := (fun k=>@current_smooth_value R h2 n U hU k).
Local Notation inc := (fun k=>smooth_test_inclusion (hE k)).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation td := (fun j=>@current_test_directional_derivative R h2 n m U hU (@coordinate_basis R n j)).
Local Notation sd := (fun j=>@current_smooth_directional_derivative R h2 n m U hU (@coordinate_basis R n j)).
Local Notation dx := (fun j=>@current_constant_form R h2 n U hU 1%N (euclidean_coordinate_form j)).
Local Notation P := (@current_test_form_product R h2 n 1%N m U hU).
Local Notation Tr := (fun a b (h:a=b)=>@current_test_degree_transport R h2 n U hU a b h).

(** Source for [current_test_exterior_coordinate_formula]:
    d psi is the original sum of DX_j wedge
    D_j psi as an equality of actual compact
    tests, supporting the boundary coordinate formula
    of Federer 4.1.7, p. 356. *)
Theorem current_test_exterior_coordinate_formula psi:
  d psi=\sum_j Tr _ _ (add1n m) (P (dx j) (td j psi)).
Proof.
apply:(smooth_test_values_extensional (hE m.+1))=>x hx.
change (value m.+1 (d psi) x=value m.+1 (\sum_j Tr _ _ (add1n m) (P (dx j) (td j psi))) x).
rewrite linear_sum fct_sumE.
apply:(can_inj (@form_includeK R X R^o m.+1)).
rewrite linear_sum.
have hLeft:form_include (value m.+1 (d psi) x)=
    \sum_j form_include (form_wedge h2 (@scalar_bilinear R) (euclidean_coordinate_form j)
      (sv m (sd j (inc m psi)) x)).
  change (form_include (sv m.+1 (inc m.+1 (d psi)) x)=
    \sum_j form_include (form_wedge h2 (@scalar_bilinear R) (euclidean_coordinate_form j)
      (sv m (sd j (inc m psi)) x))).
  rewrite (@current_test_exterior_derivative_inclusion R h2 n m U hU psi).
  exact:(@smooth_current_exterior_coordinate_values R h2 n m U hU (inc m psi) x hx).
rewrite hLeft;apply:eq_bigr=>j _.
have hTransport:=@current_test_degree_transport_values R h2 n U hU
  (1+m)%N m.+1 (add1n m) (P (dx j) (td j psi)) x.
have hIncluded:=congr1 (@form_include R X R^o m.+1) hTransport.
rewrite form_reindex_include
  (@current_test_form_product_values R h2 n 1%N m U hU (dx j) (td j psi) x hx)
  (@current_constant_form_values R h2 n U hU 1%N (euclidean_coordinate_form j) x hx) in hIncluded.
change (form_include (ev m.+1 (Tr _ _ (add1n m) (P (dx j) (td j psi))) x)=
    form_include (form_wedge h2 (@scalar_bilinear R) (euclidean_coordinate_form j)
      (sv m (inc m (td j psi)) x))) in hIncluded.
rewrite (@current_test_directional_derivative_inclusion R h2 n m U hU
  (@coordinate_basis R n j) psi) in hIncluded.
exact:esym hIncluded.
Qed.
End CurrentTestExteriorCoordinates.
