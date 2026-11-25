(** Federer (1969), 4.1.7, p. 357, and
    4.1.11, p. 366: the original E^0 is the
    unit point current on R^0. Reuse its literal
    density action, the original zero-dimensional Lebesgue
    point mass, and the existing zero-form pairing law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import BoundedHom Hom HomogeneousHom GradedComponents RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading ExteriorAlgebra ExteriorPowers FiniteExteriorPowers AlternatingSum AlternatingForms AlternatingZero AlternatingPairing
  CurrentSpaces CurrentEvaluation CurrentDirac CurrentInteriorPairing CurrentDensityAction
  EuclideanFundamentalCurrent EuclideanLebesgueDimensions PointMassIntegral MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_fundamental_current_point]:
    the empty original oriented rectangular product E^0
    is [0]=delta_0, supporting the zero-dimensional
    factorial simplex decomposition in Federer 4.1.11,
    p. 366. Its actual integral action is retained. *)
Theorem euclidean_fundamental_current_point (R:realType) (h2:(1+1:R)!=0):
  @euclidean_fundamental_current R h2 0%N=
  @dirac_current R h2 0%N (fun _=>True)
    (fun (x:R_n R 0%N) (_:True)=>@norm_full_domain_interior R (R_n R 0%N)
      (inner_norm (@euclidean_inner_productP R 0%N)) x) 0.
Proof.
pose X:=R_n R 0%N.
pose hFull:=fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R 0%N)) x.
pose w:=e_lambda (@coordinate_basis R 0%N) (ord_tuple 0%N).
have hPair (phi:A_m X R^o 0%N):pairing w phi=zero_form_value phi.
  change (form_include phi (component_val w)=zero_form_value phi).
  rewrite /w (tuple0 (ord_tuple 0%N)) e_lambdaE exterior_word_nil.
  exact:current_zero_covector_unit_value.
apply:(@current_values_extensional R h2 0%N 0%N (fun _=>True) hFull)=>psi.
rewrite dirac_current_evaluation.
have hE:=@euclidean_fundamental_current_action R h2 0%N psi.
have hPoint:=@point_mass_real_integral R X 0
  (fun x=>pairing w (@current_test_value R h2 0%N (fun _=>True) hFull 0%N psi x)).
have hValue:=congr1 (@fine R) (measure_integral_unique hE hPoint).
rewrite hPair in hValue;exact:hValue.
Qed.
