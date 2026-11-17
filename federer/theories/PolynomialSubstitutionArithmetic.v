(** Federer (1969), 3.4.7, p. 325: polynomial
    substitution preserves the ring operations. This private
    existence proof uses finite support independence and the
    actual Cauchy product; downstream work uses the sealed equations. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  PolynomialSubstitutionWitness NaturalConvolution NaturalConvolutionDegree FiniteConvolutionSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variables A B C:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable phi:{rmorphism A->C}.
Variable t:C.
Local Notation E:=(@polynomial_substitution_witness A B C embed variable coefficient hP phi t).
Local Notation bound:=(@polynomial_substitution_bound A B embed variable coefficient hP).
Local Notation support:=(@polynomial_substitution_support A B embed variable coefficient hP).
Local Notation any_bound:=(@polynomial_substitution_any_bound A B C embed variable coefficient hP phi t).

(** Source for [polynomial_substitution_additive]: evaluating
    a sum gives the sum of the original
    evaluations, supporting 3.4.7, p. 325. *)
Lemma polynomial_substitution_additive:nmod_morphism E.
Proof.
split;first exact:polynomial_substitution_zero.
move=>P Q.
pose L:=maxn (bound P) (bound Q).
have hPBound i:(L<=i)%N ->coefficient P i = 0.
  move=>hi;apply:support;exact:leq_trans (leq_maxl _ _) hi.
have hQBound i:(L<=i)%N ->coefficient Q i = 0.
  move=>hi;apply:support;exact:leq_trans (leq_maxr _ _) hi.
have hSumBound i:(L<=i)%N ->coefficient (P+Q) i = 0.
  move=>hi;by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP) hPBound // hQBound // add0r.
rewrite (any_bound hSumBound) (any_bound hPBound) (any_bound hQBound) -big_split.
apply:eq_bigr=>i _.
by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP) rmorphD mulrDl.
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build B C E polynomial_substitution_additive.

(** Source for [polynomial_substitution_multiplicative]: evaluating
    the finite Cauchy product gives the product of
    the evaluations, and the unit evaluates to the
    unit, supporting 3.4.7, p. 325. *)
Lemma polynomial_substitution_multiplicative:monoid_morphism E.
Proof.
split.
- by rewrite -(@rmorph1 A B embed) polynomial_substitution_constant rmorph1.
- move=>P Q.
  pose N:=bound P;pose M:=bound Q.
  have hN:forall i,(N<=i)%N ->coefficient P i = 0:=@polynomial_substitution_support A B embed variable coefficient hP P.
  have hM:forall i,(M<=i)%N ->coefficient Q i = 0:=@polynomial_substitution_support A B embed variable coefficient hP Q.
  have hPHigh i:(N<i)%N ->coefficient P i = 0 by move=>hi;exact:hN i (ltnW hi).
  have hQHigh i:(M<i)%N ->coefficient Q i = 0 by move=>hi;exact:hM i (ltnW hi).
  have hProductBound i:((N+M).+1<=i)%N ->coefficient (P*Q) i = 0.
    move=>hi;rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
    transitivity (natural_coefficient_convolution (coefficient P) (coefficient Q) i).
      by rewrite /natural_coefficient_convolution big_mkord.
    exact:(@natural_convolution_above_degree A (coefficient P) (coefficient Q) N M i hPHigh hQHigh hi).
  have hPhiP i:(N<=i)%N ->phi (coefficient P i) = 0 by move=>hi;rewrite hN // rmorph0.
  have hPhiQ i:(M<=i)%N ->phi (coefficient Q i) = 0 by move=>hi;rewrite hM // rmorph0.
  rewrite (any_bound hProductBound) (any_bound hN) (any_bound hM)
    (@finite_convolution_substitution_product C (fun i=>phi (coefficient P i))
      (fun i=>phi (coefficient Q i)) N M t hPhiP hPhiQ).
  apply:eq_bigr=>k _;congr (_*t^+k).
  rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP)
    rmorph_sum /natural_coefficient_convolution big_mkord.
  apply:eq_bigr=>i _;exact:rmorphM.
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build B C E polynomial_substitution_multiplicative.

(** Source for [commutative_polynomial_evaluation_exists]: the
    original coefficient map and chosen variable value
    extend to an actual polynomial ring homomorphism,
    supporting the subring in 3.4.7, p. 325. *)
Theorem commutative_polynomial_evaluation_exists:
  exists evaluate:{rmorphism B->C},is_commutative_polynomial_evaluation embed variable phi t evaluate.
Proof.
exists (GRing.RMorphism.clone B C E _);constructor.
- exact:polynomial_substitution_constant.
- exact:polynomial_substitution_variable.
Qed.
End Arithmetic.
