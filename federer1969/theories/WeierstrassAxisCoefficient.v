(** Federer (1969), 3.4.6, pp. 322–323: the
    original transverse-degree-zero coefficient is the divided
    derivative on the distinguished direction, independently
    of the transverse point. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricAlgebra SymmetricForms SymmetricDividedMonomials
  PolynomialTaylorTerms HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermJetsSealed
  AnalyticGermCoefficientForms WeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_axis_coefficient_value]: the
    original f_(i,0) is (i!)^-1 D^i f(0)[v^i]
    for every transverse point, giving the normalized
    phi_(i,0) conditions in 3.4.6, pp. 322–323. *)
Theorem weierstrass_axis_coefficient_value (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i (C:K->R):
  is_weierstrass_split_coefficient alpha v inclusion i 0%N C ->
  forall z,C z=((i`!)%:R)^-1*@ContinuousMultilinear.evaluation R i X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun _:'I_i=>v]
    (@AnalyticGermJets.value R X NX hNX 0 i alpha).
Proof.
move=>hC z.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
rewrite /is_weierstrass_split_coefficient addn0 in hC.
rewrite (hC (F i) (hF i) z) symmetric_taylor_term_value subn0.
have hZero:symmetric_divided_vector_power (inclusion z) 0%N=symmetric_unit X.
  by rewrite /symmetric_divided_vector_power fact0 invr1 scale1r /symmetric_vector_power /= symmetric_word_nil.
rewrite hZero symmetric_product_unitl.
change (sform_polynomial_value (F i) v=((i`!)%:R:R)^-1*
  @ContinuousMultilinear.evaluation R i X R^o NX (fun r=>`|r|) hNX (@scalar_absolute_value_norm R)
  [ffun _:'I_i=>v] (@AnalyticGermJets.value R X NX hNX 0 i alpha)).
rewrite sform_polynomial_diagonal_value hF.
have hTuple:[ffun s=>tnth [tuple v |s<i] s]=[ffun _:'I_i=>v].
  by apply/ffunP=>s;rewrite !ffunE tnth_mktuple.
by rewrite hTuple.
Qed.
