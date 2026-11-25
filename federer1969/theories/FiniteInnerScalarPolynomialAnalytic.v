(** Federer (1969), 3.4.5, pp. 318–321: finite
    Taylor polynomials and their local analytic compositions.
    This supporting consequence of 3.1.24, pp. 238–240,
    discharges continuity of every finite coefficient form. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm LinearBasis HilbertFormCompactness
  SymmetricForms PolynomialFunctions PolynomialRepresentations FiniteInnerSymmetricFormBounds
  ScalarNormMetricCompleteness NormAnalyticUP NormAnalyticPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_scalar_polynomial_analytic]:
    every actual finite-dimensional scalar polynomial is analytic
    on the whole original space, supporting the finite
    Taylor arguments of 3.4.5, pp. 318–321. No
    coefficient bound is assumed; finite coordinates prove it. *)
Theorem finite_inner_scalar_polynomial_analytic (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (P:PolynomialFunction X R^o):
  @norm_analytic R X R^o (inner_norm hB) (fun t=>`|t|)
    (inner_norm_real_norm hB) (@scalar_absolute_value_norm R) setT P.
Proof.
apply:(@norm_polynomial_function_analytic R X R^o (inner_norm hB) (fun t=>`|t|)
  (inner_norm_real_norm hB) (@scalar_absolute_value_norm R) (@scalar_norm_metric_complete R) P)=>i _.
exact:(@finite_inner_symmetric_form_bounded R X R^o B hB (fun t=>`|t|)
  (@scalar_absolute_value_norm R).1 n e he i _).
Qed.
