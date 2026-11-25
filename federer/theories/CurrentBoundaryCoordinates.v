(** Federer (1969), 4.1.7, p. 356: the
    original third displayed equation for current
    boundary, proved by the actual coordinate
    differential and its original transpose sign. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms CurrentSpaces
  CurrentEvaluation CurrentPointEvaluation CurrentDegreeTransport CurrentDegreeTransportInverse
  CurrentBoundary CurrentContraction CurrentConstantFields CurrentDirectionalDerivative
  CurrentConstantTestDirectional CurrentTestFormProduct CurrentTestExteriorDerivative CurrentTestExteriorCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentBoundaryCoordinates.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (fun k=>@current_space R h2 n U hU k).
Local Notation ev := (fun k=>@current_value R h2 n U hU k).
Local Notation dx := (fun j=>@current_constant_form R h2 n U hU 1%N (euclidean_coordinate_form j)).
Local Notation dir := (fun j=>@current_directional_derivative R h2 n (1+m) U hU (@coordinate_basis R n j)).
Local Notation td := (fun j=>@current_test_directional_derivative R h2 n m U hU (@coordinate_basis R n j)).
Local Notation P := (@current_contraction R h2 n 1%N m U hU).
Local Notation Q := (@current_test_form_product R h2 n 1%N m U hU).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation Tr := (fun a b (h:a=b)=>@current_degree_transport R h2 n U hU a b h).
Local Notation TTr := (fun a b (h:a=b)=>@current_test_degree_transport R h2 n U hU a b h).

(** Source for [current_boundary_coordinate_formula]:
    boundary T equals minus the sum of (D_j T)
    contracted DX_j, Federer 4.1.7, p. 356.
    The 1+m and m+1 input dimensions are
    identified explicitly, covering every positive degree. *)
Theorem current_boundary_coordinate_formula (T:C (1+m)):
  @current_boundary R h2 n m U hU (Tr _ _ (add1n m) T)=
    -\sum_j P (dx j) (dir j T).
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>psi.
have hTests:TTr _ _ (esym (add1n m)) (d psi)=\sum_j Q (dx j) (td j psi).
  rewrite (@current_test_exterior_coordinate_formula R h2 n m U hU psi) linear_sum.
  apply:eq_bigr=>j _;exact:current_test_degree_transport_inverse.
have hTerm j:ev m (P (dx j) (dir j T)) psi= -ev (1+m) T (Q (dx j) (td j psi)).
  rewrite current_contraction_evaluation current_directional_derivative_evaluation.
  by rewrite (@current_constant_test_directional_commute R h2 n 1%N m U hU
    (@coordinate_basis R n j) (euclidean_coordinate_form j) psi).
have hSum:(\sum_j ev m (P (dx j) (dir j T)) psi)=
    \sum_j -ev (1+m) T (Q (dx j) (td j psi)).
  apply:eq_bigr=>j _;exact:hTerm.
rewrite current_boundary_evaluation current_degree_transport_evaluation hTests linear_sum.
rewrite current_value_negate current_value_finite_sum.
by rewrite hSum sumrN opprK.
Qed.
End CurrentBoundaryCoordinates.
