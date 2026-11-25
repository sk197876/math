(** Federer (1969), 4.1.7, pp. 355–359:
    the actual vector-interior test operator
    shrinks support. Reuse the original
    fixed-support multiplier law and the
    proved test-lift support theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentVectorSpaces CurrentSupportGeometry
  CurrentTestVectorInterior SupportedSmoothOperatorSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_test_vector_interior_support]:
    multiplication by a smooth vector field
    preserves the input test support bound,
    supporting the support and constancy
    assertions in Federer 4.1.7, pp. 355–359. *)
Theorem current_test_vector_interior_support (R:realType) (h2:(1+1:R)!=0) n k p
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (xi:@current_vector_smooth_space R h2 n U hU k)
    (psi:@current_test_space R h2 n U hU (k+p)):
  @current_test_support R h2 n p U hU (@current_test_vector_interior R h2 n k p U hU xi psi)
    `<=` @current_test_support R h2 n (k+p) U hU psi.
Proof.
rewrite /current_test_support /current_test_vector_interior.
exact:supported_smooth_test_support_subset.
Qed.
