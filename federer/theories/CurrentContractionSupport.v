(** Federer (1969), 4.1.7, pp. 355–359:
    contraction by a smooth form
    cannot enlarge the original current
    support. This supporting locality consequence
    of the original test transpose
    is needed for proper pushforward projection. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentContraction CurrentTestFormProduct CurrentSupportGeometry TestDualOperatorSupport
  SupportedSmoothOperatorSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentContractionSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable phi:@current_smooth_space R h2 n U hU k.
Local Notation DT := (fun d=>@current_test_space R h2 n U hU d).
Local Notation value := (fun d=>@current_test_value R h2 n U hU d).
Local Notation action := (fun d=>@current_value R h2 n U hU d).
Local Notation multiply := (@current_test_form_product R h2 n k p U hU phi).
Local Notation contract := (@current_contraction R h2 n k p U hU phi).

(** Source for [current_test_form_product_support_subset]:
    the original compact test product
    shrinks its test factor's support,
    supporting the transpose locality in
    Federer 4.1.7, pp. 355–359. *)
Lemma current_test_form_product_support_subset psi:
  @current_test_support R h2 n (k+p) U hU (multiply psi) `<=`
    @current_test_support R h2 n p U hU psi.
Proof.
rewrite /current_test_support /current_test_form_product.
exact:supported_smooth_test_support_subset.
Qed.

(** Source for [current_contraction_support_subset]:
    the support of T contracted
    with phi is contained in
    spt T, supporting the proper
    projection formula of Federer 4.1.7,
    p. 359, from the original
    operations on pp. 355–356. *)
Theorem current_contraction_support_subset (T:@current_space R h2 n U hU (k+p)):
  @current_support R h2 n U hU p (contract T) `<=`
    @current_support R h2 n U hU (k+p) T.
Proof.
apply:(@test_dual_operator_support_subset R X (A_m X R^o p) (A_m X R^o (k+p)) NX hNX U
  (DT p) (DT (k+p)) (value p) (value (k+p)) multiply (action (k+p) T) (action p (contract T))).
- exact:(@current_contraction_evaluation R h2 n k p U hU phi T).
- exact:current_test_form_product_support_subset.
Qed.
End CurrentContractionSupport.
