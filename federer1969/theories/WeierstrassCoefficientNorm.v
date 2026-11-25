(** Federer (1969), 3.4.6, p. 323: the actual
    mixed divided coefficient has the original factorial norm
    estimate. The original direction need not have norm one. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
From Federer Require Import ContinuousMultilinearUP ContinuousMultilinearSealed Hom RealNormUP SymmetricForms PolynomialTaylorTerms PolynomialDiagonalNorm
  HomogeneousPolynomialFunctions SymmetricOperatorNorm SymmetricOperatorTupleBound WhitneyPolynomialDifferenceBound
  AnalyticGermUP AnalyticGermJetsSealed WeierstrassCoefficientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficient_norm_bound]:
    the original bound ||f_(i,j)||<=||D^(i+j)f(0)||/(i!j!),
    with the factor ||v||^i retained before normalization,
    3.4.6, p. 323. Inclusion preserves the
    transverse norm. No finite-dimensional hypothesis is used. *)
Theorem weierstrass_split_coefficient_norm_bound (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (alpha:analytic_germ_space hNX (0:X))
    (v:X) (inclusion:Hom K X) i j (C:K->R) (F:S_m X R^o (i+j)) (L:R):
  is_weierstrass_split_coefficient alpha v inclusion i j C ->
  (forall t,F t=@ContinuousMultilinear.evaluation R (i+j)%N X R^o NX (fun r=>`|r|)
    hNX (@scalar_absolute_value_norm R) [ffun s=>tnth t s]
    (@AnalyticGermJets.value R X NX hNX 0 (i+j)%N alpha)) ->
  (forall z,NX (inclusion z)=NK z) ->
  (symmetric_operator_norm hNX.1 (fun r:R^o=>(`|r|)%R) F<=L%:E)%E ->
  forall z,`|C z|<=L*NX v^+i*NK z^+j/((i`!)%:R*(j`!)%:R).
Proof.
move=>hC hF hNorm hBound z.
have hDegree:(j<=i+j)%N by rewrite leq_addl.
have hContraction:=@symmetric_taylor_term_operator_bound R X R^o NX (fun r=>`|r|)
  hNX (@scalar_absolute_value_norm R) (i+j)%N j hDegree F v L hBound.
rewrite addnK in hContraction.
have hEvaluation:=@symmetric_operator_finite_tuple_bound R X R^o NX (fun r=>`|r|)
  hNX (@scalar_absolute_value_norm R).1 j (symmetric_taylor_term j F v)
  (L*(NX v^+i/(i`!)%:R)) hContraction [tuple inclusion z | s<j].
have hProduct:(\prod_(s<j) NX (tnth [tuple inclusion z | t<j] s))=NK z^+j.
  under eq_bigr do rewrite tnth_mktuple hNorm.
  by rewrite prodr_const card_ord.
rewrite hProduct in hEvaluation.
rewrite (hC F hF z) sform_polynomial_diagonal_value.
change (`|((j`!)%:R:R)^-1* (symmetric_taylor_term j F v [tuple inclusion z | s<j])|<=
  L*NX v^+i*NK z^+j/((i`!)%:R*(j`!)%:R)).
rewrite normrM normfV normr_nat.
have hInvNonnegative:0<=((j`!)%:R:R)^-1 by rewrite invr_ge0 ler0n.
have hBoundFinal:=ler_wpM2l hInvNonnegative hEvaluation.
have hRight:((j`!)%:R:R)^-1*(L*(NX v^+i/(i`!)%:R)*NK z^+j)=
    L*NX v^+i*NK z^+j/((i`!)%:R*(j`!)%:R).
  rewrite invfM;ring.
by rewrite hRight in hBoundFinal.
Qed.
