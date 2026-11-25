(** Federer (1969), 4.1.14, p. 370: two source
    neighbourhoods may be replaced by their intersection.
    Actual current restriction is transitive, by the original
    zero-extension action of 4.1.1, p. 345, and
    4.1.7, pp. 357–359. No representation is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCoefficientNorms CurrentEvaluation
  CurrentOpenRestriction SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_open_restriction_transitive]: the
    same actual current on a smaller original source
    is obtained directly or through an intermediate open
    source, supporting Federer 4.1.14, p. 370.
    The direct inclusion proof is arbitrary; no equality
    of inclusion witnesses is assumed. *)
Theorem current_open_restriction_transitive (R:realType) (h2:(1+1:R)!=0)
    n m (W Z U:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hWZ:forall x,W x->Z x)
    (hZU:forall x,Z x->U x)
    (hWU:forall x,W x->U x)
    (T:@current_space R h2 n U hU m):
  @current_open_restriction R h2 n m W Z hW hZ hWZ
    (@current_open_restriction R h2 n m Z U hZ hU hZU T)=
  @current_open_restriction R h2 n m W U hW hU hWU T.
Proof.
apply:(@current_values_extensional R h2 n m W hW)=>phi.
rewrite !current_open_restriction_evaluation.
apply:(congr1 (@current_value R h2 n U hU m T)).
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 n U hU m))
  =>x hx.
change (@current_test_value R h2 n U hU m
    (@current_open_test_extension R h2 n m Z U hZ hU hZU
      (@current_open_test_extension R h2 n m W Z hW hZ hWZ phi)) x=
  @current_test_value R h2 n U hU m
    (@current_open_test_extension R h2 n m W U hW hU hWU phi) x).
by rewrite !current_open_test_extension_values.
Qed.
