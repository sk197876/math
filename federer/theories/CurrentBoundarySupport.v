(** Federer (1969), 4.1.7, pp. 356–359:
    the original boundary is supported in
    the current support. Locality of the
    actual test differential and the earlier
    transpose-support law prove the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentBoundary CurrentTestExteriorDerivative CurrentSupportGeometry SupportedSmoothOperatorSupport
  TestDualOperatorSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentBoundarySupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun d=>A_m X R^o d).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C := (fun d=>@current_space R h2 n U hU d).
Local Notation DT := (fun d=>@current_test_space R h2 n U hU d).
Local Notation value := (fun d=>@current_test_value R h2 n U hU d).
Local Notation action := (fun d=>@current_value R h2 n U hU d).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation bd := (@current_boundary R h2 n m U hU).

(** Source for [current_test_exterior_support_subset]:
    the actual original test differential shrinks
    support, supporting boundary locality in
    Federer 4.1.7, pp. 356–359. *)
Theorem current_test_exterior_support_subset (phi:DT m):
  @current_test_support R h2 n m.+1 U hU (d phi) `<=`
    @current_test_support R h2 n m U hU phi.
Proof.
rewrite /current_test_support /current_test_exterior_derivative.
exact:supported_smooth_test_support_subset.
Qed.

(** Source for [current_boundary_support_subset]: the
    original boundary has support in the
    current support, supporting normality and
    proper pushforward in Federer 4.1.7,
    pp. 358–359. *)
Theorem current_boundary_support_subset (T:C m.+1):
  @current_support R h2 n U hU m (bd T) `<=` @current_support R h2 n U hU m.+1 T.
Proof.
apply:(@test_dual_operator_support_subset R X (Y m) (Y m.+1) NX hNX U
  (DT m) (DT m.+1) (value m) (value m.+1) d (action m.+1 T) (action m (bd T))).
- exact:(@current_boundary_evaluation R h2 n m U hU T).
- exact:current_test_exterior_support_subset.
Qed.
End CurrentBoundarySupport.
