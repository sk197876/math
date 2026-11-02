(** Federer (1969), 3.1.24, p. 240: the affine
    and quadratic scalar functions appearing in the explicit
    inverse expression are analytic polynomials. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets ring.
From Federer Require Import TensorUP RealNormUP ScalarNormMetricCompleteness SymmetricForms SymmetricFormSum
  SymmetricFunctionalProduct SymmetricPolynomialEvaluation HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  PolynomialFunctions NormAnalyticUP NormAnalyticDomain ScalarPolynomialAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_power_polynomial_exists]: the scalar
    powers in the inverse formula of Federer 3.1.24, p. 240,
    are polynomial functions in the intrinsic Chapter 1 sense.
    The factorial-scaled product form proves existence of a
    representation; no new polynomial object is postulated. *)
Theorem scalar_power_polynomial_exists (R:realType) m :
  exists P:PolynomialFunction R^o R^o,forall x:R,P x= x^+m.
Proof.
pose phi:=(m`!)%:R*:symmetric_functional_product_form (linear_id R^o) m.
exists (polynomial_from_forms (sform_include phi))=>x.
rewrite polynomial_from_formsE symmetric_polynomial_value_include
  sform_polynomial_diagonal_value /phi sform_scaleE symmetric_functional_product_formE.
have he:(\prod_(i<m) (linear_id R^o) (tnth [tuple x | j<m] i))= x^+m.
  under eq_bigr do rewrite tnth_mktuple.
  change ((\prod_(i<m) x)= x^+m).
  by rewrite big_const_ord iter_mulr_1.
rewrite he.
change ((m`!)%:R^-1*((m`!)%:R*x^+m)=x^+m).
rewrite mulrA mulVf ?mul1r //.
by rewrite pnatr_eq0 -lt0n fact_gt0.
Qed.

(** Source for [scalar_power_analytic_at]: integer powers,
    including the constant power zero, are analytic on the
    real line, supporting the affine and quadratic terms in
    Federer 3.1.24, p. 240. *)
Theorem scalar_power_analytic_at (R:realType) m (a:R) :
  @norm_analytic_at R R^o R^o (fun t=>`|t|) (fun t=>`|t|)
    (scalar_absolute_value_norm R) (scalar_absolute_value_norm R) setT (fun x=>x^+m) a.
Proof.
have [P hP]:=@scalar_power_polynomial_exists R m.
pose hN:=scalar_absolute_value_norm R.
have hp:=@scalar_polynomial_function_analytic R R^o (fun t=>`|t|) hN
  (@scalar_norm_metric_complete R) P a Logic.I.
exact (@norm_analytic_at_domain_agreement R R^o R^o (fun t=>`|t|) (fun t=>`|t|) hN hN
  setT P (fun x=>x^+m) a (fun x _=>hP x) hp).
Qed.
