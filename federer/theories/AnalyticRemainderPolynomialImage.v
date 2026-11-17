(** Federer (1969), 3.4.7, p. 325: actual analytic
    division remainders are finite transverse polynomials.
    The independently proved bounded polynomial-image module
    and original remainder theorem prove this assertion;
    polynomial membership is not an additional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing WeierstrassTransverseUP WeierstrassTransversePullback
  WeierstrassDivisionUP WeierstrassRemainderModule CommutativePolynomialUP
  CommutativePolynomialEvaluationUP PolynomialBoundedEvaluationModule RingScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RemainderImage.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [analytic_directional_remainder_polynomial_image]:
    every actual remainder of directional order below k
    lies in the original polynomial subring, with every
    coefficient of degree at least k zero, supporting
    the factor argument in 3.4.7, p. 325. *)
Theorem analytic_directional_remainder_polynomial_image k (rho:G):
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall x,analytic_representative_value fXi x = xi x) ->
  @is_directional_polynomial_germ R X NX hNX k v rho ->
  exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\rho = J P.
Proof.
move=>hXi hXiValues hRemainder.
have hModule:=@bounded_polynomial_image_submodule A B G embed variable coefficient
  hP E Gamma J hJ k.
have hGenerators i (hi:(i<k)%N):exists P:B,
    (forall j,(k<=j)%N ->coefficient P j = 0) /\Gamma^+i = J P.
  exact:(@bounded_polynomial_image_contains_power A B G embed variable coefficient
    hP E Gamma J hJ k i hi).
exact:(@weierstrass_remainder_in_transverse_module R X K NX NK hNX hNK
  v xi inclusion projection hSplit k fXi
  (fun x=>exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\x = J P)
  rho hXi hXiValues hModule hGenerators hRemainder).
Qed.
End RemainderImage.
