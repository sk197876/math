(** Federer (1969), 4.1.7, p. 356: zero
    smooth coefficient fields give zero test products,
    supporting the constant-coordinate current equations. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct ScalarCoefficients
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestEvaluation CurrentTestFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_test_form_product_zero_left]:
    zero wedge psi is the actual zero test,
    supporting Federer 4.1.7, p. 356, by
    the original bilinearity of 1.4.2, p. 18. *)
Theorem current_test_form_product_zero_left (R:realType) (h2:(1+1:R)!=0) n k p
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x) psi:
  @current_test_form_product R h2 n k p U hU 0 psi=0.
Proof.
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 n U hU (k+p)))=>x hx.
have hP:=@current_test_form_product_values R h2 n k p U hU 0 psi x hx.
have hZero:=smooth_function_zero_value (@current_smooth_space_laws R h2 n U hU k) x.
change (@current_test_value R h2 n U hU (k+p)
  (@current_test_form_product R h2 n k p U hU 0 psi) x=
    @current_test_value R h2 n U hU (k+p) 0 x).
rewrite hP hZero (bil0l (@form_wedge_bilinear R h2 (R_n R n) R^o
  (fun a b=>a*b) (@scalar_bilinear R) k p)).
change (0=smooth_test_values_hom (@current_smooth_space_laws R h2 n U hU (k+p)) 0 x).
by rewrite GRing.Theory.linear0.
Qed.
