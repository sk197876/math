(** Federer (1969), 4.1.15, p. 373: identify the actual
    point one-current with the literal printed product
    delta_0 wedge e_1, using the earlier sealed vector
    product and its original test action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation
  CurrentDirac CurrentConstantFields CurrentZeroVectorProduct
  PointMultivectorCurrentSealed PointOneCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointOneCurrentProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation unit:=(e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N)).

(** Source for [point_one_current_dirac_vector_product]: the
    literal T=delta_0 wedge e_1 definition in 4.1.15,
    p. 373, on the actual original current spaces. *)
Theorem point_one_current_dirac_vector_product:
  @point_one_current R h2=
    @current_zero_vector_product R h2 1%N 1%N Full hFull
      (@current_constant_vector R h2 1%N Full hFull 1%N unit)
      (@dirac_current R h2 1%N Full hFull (0:X)).
Proof.
apply:(@current_values_extensional R h2 1%N 1%N Full hFull)=>phi.
rewrite current_zero_vector_product_evaluation dirac_current_evaluation
  current_zero_test_vector_values;last exact:Logic.I.
rewrite current_constant_vector_values;last exact:Logic.I.
by rewrite /point_one_current (@PointMultivectorCurrent.laws R h2
  1%N 1%N Full hFull (0:X) Logic.I).
Qed.
End PointOneCurrentProduct.
