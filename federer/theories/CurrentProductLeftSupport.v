(** Federer (1969), 4.1.12, p. 368: a
    multiplied test has support in its scalar
    multiplier's support. The actual alternating product
    and the original closure definition of support
    prove this locality law in every degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentSpaces CurrentCoefficientNorms
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentTestFormProduct CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProductLeftSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation sv d := (@current_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_smooth_space_laws R h2 n U hU d).
Local Notation DT d := (@current_test_space R h2 n U hU d).
Local Notation value d := (@current_test_value R h2 n U hU d).
Local Notation product := (@current_test_form_product R h2 n k p U hU).

(** Source for [current_test_form_product_left_support]:
    spt(phi wedge psi) is contained in the
    original spt phi, supporting the subordinate
    pieces of the partition argument in Federer
    4.1.12, p. 368. The left multiplier need
    not itself have compact support. *)
Theorem current_test_form_product_left_support (phi:E k) (psi:DT p):
  @current_test_support R h2 n (k+p) U hU (product phi psi) `<=`
    @smooth_function_support R X (A_m X R^o k) NX hNX U (E k) (sv k) phi.
Proof.
move=>x [hUx hClosure];split;first exact:hUx.
apply:(@closureS XT [set y:XT|value (k+p) (product phi psi) y<>0]
  [set y:XT|sv k phi y<>0] _ x hClosure).
move=>y hNonzero hZero.
case:(pselect (U y))=>hy.
- have h:=@current_test_form_product_values R h2 n k p U hU phi psi y hy.
  rewrite hZero (bil0l (@form_wedge_bilinear R h2 X R^o _ (scalar_bilinear R) k p)) in h.
  exact:hNonzero h.
- exact:(hNonzero (@smooth_test_value_outside R X (A_m X R^o (k+p)) NX
    (@current_form_comass R h2 n (k+p)) hNX (@current_form_comass_real_norm R h2 n (k+p))
    U (E (k+p)) (sv (k+p)) (hE (k+p)) (product phi psi) y hy)).
Qed.
End CurrentProductLeftSupport.
