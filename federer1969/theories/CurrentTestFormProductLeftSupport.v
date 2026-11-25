(** Federer (1969), 4.1.7, pp. 355–356,
    used in the cutoff formula of 4.1.14,
    p. 371: multiplication by an original compact
    form test cannot enlarge the first factor's
    support. Use the original pointwise exterior
    product and closure monotonicity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingProduct ScalarCoefficients CurrentSpaces
  CurrentSupportGeometry CurrentTestFormProduct SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_test_form_product_left_support]:
    spt(gamma wedge psi) is contained in
    spt gamma, supporting the original local
    composition law of Federer 4.1.14, p. 371,
    by 4.1.7, pp. 355–356. Both degrees
    and dimension zero are retained. *)
Theorem current_test_form_product_left_support
    (R:realType) (h2:(1+1:R)!=0) n k p
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:@current_test_space R h2 n U hU k)
    (psi:@current_test_space R h2 n U hU p):
  @current_test_support R h2 n (k+p)%N U hU
    (@current_test_form_product R h2 n k p U hU
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU k) gamma) psi)
    `<=` @current_test_support R h2 n k U hU gamma.
Proof.
move=>x [hx hClosure];split;first exact:hx.
apply:(@closureS (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R n)))
  [set y|@current_test_value R h2 n U hU (k+p)%N
    (@current_test_form_product R h2 n k p U hU
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU k) gamma) psi) y<>0]
  [set y|@current_test_value R h2 n U hU k gamma y<>0] _ x hClosure).
move=>y hNonzero hZero;apply:hNonzero.
case:(pselect (U y))=>[hy|hy].
- rewrite (@current_test_form_product_values R h2 n k p U hU _ psi y hy).
  change (form_wedge h2 (scalar_bilinear R)
    (@current_test_value R h2 n U hU k gamma y)
    (@current_test_value R h2 n U hU p psi y)=0).
  by rewrite hZero (bil0l (@form_wedge_bilinear R h2 (R_n R n) R^o _
    (scalar_bilinear R) k p)).
- exact:(smooth_test_value_outside (@current_smooth_space_laws R h2 n U hU (k+p)%N)
    (@current_test_form_product R h2 n k p U hU
      (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU k) gamma) psi) hy).
Qed.
