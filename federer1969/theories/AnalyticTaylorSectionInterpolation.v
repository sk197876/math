(** Supporting Federer (1969), 3.4.8(5), p. 328:
    exact interpolation by the original finite Taylor polynomial.
    The independent value laws, actual polynomial derivatives and
    the divided-monomial coordinate duality supply the right inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum RealNormUP
  InnerProductUP InnerNorm HilbertFormCompactness LinearBasis SymmetricForms SymmetricFormSum
  SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials SymmetricDividedBasis
  SymmetricMonomialTuples SymmetricCoordinateDualBasis SymmetricPairing
  PolynomialFunctions PolynomialRepresentations ContinuousMultilinearSealed AnalyticGermRing
  AnalyticGermJetsSealed FiniteJetDegreeIndices AnalyticFiniteCoefficientsUP
  AnalyticPolynomialGermUP AnalyticPolynomialGermJets AnalyticTaylorSectionUP
  AnalyticTaylorSectionExistence SymmetricOrdinalSumComponent SymmetricMonomialCoefficientPairing
  SymmetricCoordinateSynthesisPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Interpolation.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable l:nat.
Local Notation W:=[the lmodType R of {ffun finite_jet_degree_indices n l->R^o}].
Variable J:PolynomialFunction X R^o->G.
Hypothesis hJ:is_analytic_polynomial_germ_map J.
Variable T:W->G.
Hypothesis hT:is_analytic_finite_taylor_section he J T.
Variable f:G->W.
Hypothesis hF:is_analytic_finite_coefficient_map e f.

(** Source for [analytic_finite_taylor_section_interpolation]: supporting
    original quotient dimension comparison for Federer 3.4.8(5), p. 328.
    The original Taylor polynomial has exactly the prescribed finite
    normalized derivative coefficients. Degree and dimension zero remain. *)
Theorem analytic_finite_taylor_section_interpolation c:f (T c) = c.
Proof.
apply/ffunP;case=>k b.
rewrite hF (analytic_finite_taylor_section_formula hT).
rewrite (@analytic_polynomial_germ_origin_coefficients R X B hB n e he J hJ).
rewrite /finite_taylor_polynomial_witness (polynomial_from_formsK (@pchar_num R))
  sform_ordinal_sum_component.
have hTuple:
    [tuple finite_jet_monomial_arguments e
      (existT (fun h:'I_l=>symmetric_indices n (val h)) k b) i | i<k] =
    symmetric_monomial_tuple e b.
  apply:eq_from_tnth=>i;by rewrite tnth_mktuple /finite_jet_monomial_arguments ffunE.
rewrite hTuple /finite_jet_degree_multiindex /=
  -symmetric_normalized_monomial_form_pairing /finite_taylor_coefficient_form.
exact:(symmetric_coordinate_synthesis_pairing (@pchar_num R)).
Qed.
End Interpolation.
