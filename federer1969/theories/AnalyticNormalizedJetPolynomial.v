(** Federer (1969), 3.4.11, p. 338:
    each actual germ jet gives its exact normalized
    homogeneous polynomial function. Reuse the existing actual
    coefficient forms and their polynomial evaluation; finite
    source dimension supplies analyticity without a new bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis SymmetricForms SymmetricFormSum SymmetricPolynomialEvaluation PolynomialFunctions
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm ContinuousMultilinearUP
  ContinuousMultilinearSealed AnalyticGermUP AnalyticGermJetsSealed
  AnalyticGermCoefficientForms FiniteInnerScalarPolynomialAnalytic NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_normalized_jet_polynomial_exists]: the
    polynomial corresponding to D^k phi(0) in
    3.4.11, p. 338, with its original
    factorial normalization. Every order and ambient dimension
    remain, including degree zero. *)
Theorem analytic_normalized_jet_polynomial_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) k
    (alpha:analytic_germ_space (inner_norm_real_norm hB) (0:X)):
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  exists P:PolynomialFunction X R^o,
    @is_homogeneous_polynomial R X R^o k P /\
    @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) setT P /\
    forall v,P v=(k`!)%:R^-1*:@ContinuousMultilinear.evaluation R k X R^o NX
      (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) [ffun _=>v]
      (@AnalyticGermJets.value R X NX hNX 0 k alpha).
Proof.
move=>NX hNX.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
pose P:=polynomial_from_forms (sform_include (F k)).
have hValue v:P v=sform_polynomial_value (F k) v.
  by rewrite /P polynomial_from_formsE symmetric_polynomial_value_include.
exists P;split;first by exists (F k).
split;first exact:(@finite_inner_scalar_polynomial_analytic R X B hB n e he P).
move=>v;rewrite hValue sform_polynomial_diagonal_value hF.
congr (_*:_).
congr (@ContinuousMultilinear.evaluation R k X R^o NX (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) _ _).
by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
Qed.
