(** Federer (1969), 4.1.7, p. 356: actual
    test derivatives retain their original smooth
    representatives, as required by the product rules. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothTestSpaces TestDirectionalOperator CurrentDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_test_directional_derivative_inclusion]:
    the actual test and smooth D_v agree under the
    original inclusion, supporting Federer 4.1.7,
    p. 356, by 4.1.1, p. 346. *)
Lemma current_test_directional_derivative_inclusion (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    v phi:
  smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m)
    (@current_test_directional_derivative R h2 n m U hU v phi)=
  @current_smooth_directional_derivative R h2 n m U hU v
    (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU m) phi).
Proof. exact:test_directional_evaluation. Qed.
