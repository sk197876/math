(** Federer (1969), 3.4.11, p. 338:
    the actual first nonzero derivative gives the
    original homogeneous polynomial. Its positive degree is
    proved from the germ's zero value at the centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis PolynomialFunctions HomogeneousPolynomialFunctions NormAnalyticUP
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermRing
  AnalyticGermJetsSealed AnalyticGermFirstNonzeroJet AnalyticGermValueSealed
  AnalyticGermValueZerothJet AnalyticInitialPolynomialUP AnalyticNormalizedJetPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_polynomial_exists]: the
    choice of the least nonzero derivative and its
    normalized polynomial in 3.4.11, p. 338.
    No order, regular direction or nonzero polynomial
    is supplied as an additional hypothesis. *)
Theorem analytic_initial_polynomial_exists (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (alpha:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0):
  alpha<>0 ->@AnalyticGermValue.map R X (inner_norm hB) (inner_norm_real_norm hB) 0 alpha=0 ->
  exists k (P:PolynomialFunction X R^o),
    is_initial_analytic_germ_polynomial alpha k P /\
    @is_homogeneous_polynomial R X R^o k P /\
    @norm_analytic R X R^o (inner_norm hB) (fun t:R^o=>`|t|)
      (inner_norm_real_norm hB) (@scalar_absolute_value_norm R) setT P.
Proof.
move=>hNonzero hValue.
have hZero:=(@analytic_germ_value_zeroth_jet R X (inner_norm hB)
  (inner_norm_real_norm hB) 0 alpha).1 hValue.
have [k [hTop hLower]]:=@analytic_germ_first_nonzero_jet R X (inner_norm hB)
  (inner_norm_real_norm hB) 0 alpha hNonzero.
have hPositive:(0<k)%N.
  case:k hTop hLower=>[|k] hTop hLower;last by [].
  exfalso;exact:hTop hZero.
have [P [hPolynomial [hAnalytic hFormula]]]:=
  @analytic_normalized_jet_polynomial_exists R X B hB n e he k alpha.
exists k,P;split;last by split.
by split;last split;last split.
Qed.
