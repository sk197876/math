(** Federer (1969), 3.4.7, p. 325: the
    original transverse polynomial algebra embeds faithfully in
    the analytic germ ring. Local coefficient independence
    supplies injectivity; it is not an algebraic premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  WeierstrassTransverseUP WeierstrassTransversePullback AnalyticTransverseCoefficientIndependence
  CommutativePolynomialUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Injection.
Variable R:realType.
Variables X K:lmodType R.
Variable NX:X->R.
Variable NK:K->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNK:is_real_norm NK.
Variable v:X.
Variable xi:Hom X R^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).

(** Source for [analytic_transverse_polynomial_evaluation_injective]:
    the original xi germ is transcendental over the
    transverse germ ring, so its polynomial evaluation
    is injective, as asserted in 3.4.7, p. 325. *)
Theorem analytic_transverse_polynomial_evaluation_injective (B:comNzRingType)
    (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
    (hP:is_commutative_polynomial_ring embed variable coefficient)
    (J:{rmorphism B->G}) (hJ:is_commutative_polynomial_evaluation embed variable E Gamma J):
  (forall x,analytic_representative_value fXi x = xi x) ->injective J.
Proof.
move=>hXi.
have hKernel (P:B):J P = 0 ->P = 0.
  move=>hZero.
  have [N hN]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
  have hSum:(\sum_(i<N) E (coefficient P i)*Gamma^+i) = 0.
    rewrite -(@polynomial_evaluation_finite_expression A B G embed variable coefficient hP E Gamma J hJ P N hN).
    exact:hZero.
  have hCoefficients:=@analytic_transverse_coefficients_independent R X K NX NK hNX hNK
    v xi inclusion projection hSplit fXi N (coefficient P) hXi hSum.
  apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
  rewrite (@polynomial_coefficient_zero A B embed variable coefficient hP).
  case:(ltnP i N)=>hi;[exact:hCoefficients i hi|exact:hN i hi].
move=>P Q hEqual.
have hDifference:J (P-Q) = 0 by rewrite rmorphB hEqual subrr.
exact:subr0_eq (hKernel (P-Q) hDifference).
Qed.
End Injection.
