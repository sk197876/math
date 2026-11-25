(** Federer (1969), 4.1.7, p. 356: the
    original smooth divergence is the sum of
    coordinate derivatives contracted DX_j. Reuse the
    exact algebraic formula from 4.1.6, p. 354. *)
From mathcomp Require Import functions all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  CurrentCoefficientNorms CurrentVectorSpaces CurrentDivergenceMap SmoothCurrentDivergence
  OneCovectorInterior CurrentVectorDirectionalDerivative CurrentOneCovectorMap SmoothCurrentOneCovector
  ContinuousMultilinearSealed ContinuousMultilinearOne DivergenceCoordinates
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothDirectionalDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothCurrentDivergenceCoordinates.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation V := (fun j=>@current_vector_smooth_space R h2 n U hU j).
Local Notation vv := (fun j=>@current_vector_smooth_value R h2 n U hU j).
Local Notation hV := (fun j=>@current_vector_smooth_space_laws R h2 n U hU j).
Local Notation div := (@smooth_current_divergence R h2 n p U hU).
Local Notation dir := (fun j=>@current_vector_smooth_directional_derivative R h2 n p.+1 U hU
  (@coordinate_basis R n j)).
Local Notation cut := (fun j=>@smooth_current_one_covector R h2 n p U hU (euclidean_coordinate_form j)).

(** Source for [smooth_current_divergence_coordinate_formula]:
    the original sum div xi=sum_j D_j xi
    contracted DX_j holds in the actual smooth
    field space, supporting Federer 4.1.7, p. 356. *)
Theorem smooth_current_divergence_coordinate_formula (xi:V p.+1):
  div xi=\sum_j cut j (dir j xi).
Proof.
apply:(smooth_function_extensional (hV p))=>x hx.
rewrite (smooth_current_divergence_values xi hx).
change (@current_divergence_map R h2 n p
    (@current_vector_smooth_derivatives R h2 n U hU p.+1 1%N x xi)=
  smooth_function_values_hom (hV p) (\sum_j cut j (dir j xi)) x).
rewrite /current_divergence_map hom_compE divergence_coordinate_formula linear_sum fct_sumE.
apply:eq_bigr=>j _.
have hValue:smooth_function_values_hom (hV p) (cut j (dir j xi)) x=
    positive_one_covector_interior h2 (vv p.+1 (dir j xi) x) (euclidean_coordinate_form j).
  exact:(@smooth_current_one_covector_values R h2 n p U hU
    (euclidean_coordinate_form j) (dir j xi) x hx).
apply:(eq_trans _ (esym hValue)).
rewrite (@current_vector_smooth_directional_derivative_laws R h2 n p.+1 U hU
  (@coordinate_basis R n j) xi x hx).
by [].
Qed.
End SmoothCurrentDivergenceCoordinates.
