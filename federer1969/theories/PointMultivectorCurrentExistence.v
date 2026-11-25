(** Federer (1969), 4.1.9, p. 363: existence of the
    original point multivector current. Reuse the actual Dirac
    current and multiplication by a constant multivector from
    4.1.7, pp. 355–356 and 359. The construction serves
    only this existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentConstantFields CurrentDirac CurrentZeroVectorProduct PointMultivectorCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointMultivectorCurrentExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable x:X.
Hypothesis hx:U x.
Local Notation C := (@current_space R h2 n U hU j).

(** Source for [point_multivector_current_exists]: the current
    beta to <eta,beta(x)> exists for every original x and
    eta, supporting the pointwise derivation of the form
    homotopy formula in Federer 4.1.9, p. 363. *)
Theorem point_multivector_current_exists:
  exists P:Hom (exterior_power X j) C,@is_point_multivector_current R h2 n j U hU x P.
Proof.
pose P:=hom_comp (@current_zero_vector_field_product R h2 n j U hU (@dirac_current R h2 n U hU x))
  (@current_constant_vector R h2 n U hU j).
exists P=>eta beta.
rewrite /P hom_compE current_zero_vector_product_evaluation dirac_current_evaluation.
rewrite (@current_zero_test_vector_values R h2 n j U hU
  (@current_constant_vector R h2 n U hU j eta) beta x hx).
by rewrite (@current_constant_vector_values R h2 n U hU j eta x hx).
Qed.
End PointMultivectorCurrentExistence.
