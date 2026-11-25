(** Federer (1969), 3.4.7, p. 325, using
    3.4.6(1), p. 322: analytic division has
    actual polynomial remainders in the original transverse
    subring. Its uniqueness gives the zero-remainder test
    used to transfer primality, without assuming that test. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing WeierstrassTransverseUP WeierstrassTransversePullback
  WeierstrassRegularUP WeierstrassDivisionUP WeierstrassDivisionWithTransverse
  AnalyticRemainderPolynomialImage AnalyticPolynomialRemainderFromSupport
  AnalyticTransversePolynomialInjection CommutativePolynomialUP CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ActualDivision.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Hypothesis hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Hypothesis hXiValues:forall x,analytic_representative_value fXi x = xi x.
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

(** Source for [analytic_polynomial_division_exists]: actual
    analytic division by the original regular polynomial
    gives a finite polynomial remainder of the required
    support, expanding 3.4.7, p. 325. *)
Theorem analytic_polynomial_division_exists (H:B) n:
  @is_weierstrass_regular_germ R X NX hNX (J H) n v ->
  forall x:G,exists a:G,exists r:B,
    (forall i,(n<=i)%N ->coefficient r i = 0) /\x = a*J H+J r.
Proof.
move=>hRegular x.
have [a [t [hDivision hUnique]]]:=@weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection n (J H) x hSplit hXi hRegular.
have [r [hBound hT]]:=@analytic_directional_remainder_polynomial_image R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embed variable coefficient hP J hJ n t
  hXi hXiValues (weierstrass_division_polynomial_remainder hDivision).
exists a,r;split;first exact:hBound.
by rewrite (weierstrass_division_identity hDivision) hT.
Qed.

(** Source for [analytic_polynomial_zero_remainder_unique]:
    an actual polynomial remainder in a zero analytic
    division is zero, by the proved original uniqueness
    and faithful coefficient embedding, supporting 3.4.7,
    p. 325. No quotient or primality conclusion is assumed. *)
Theorem analytic_polynomial_zero_remainder_unique (H:B) n:
  @is_weierstrass_regular_germ R X NX hNX (J H) n v ->
  forall (a:G) (r:B),(forall i,(n<=i)%N ->coefficient r i = 0) ->
    0 = a*J H+J r ->r = 0.
Proof.
move=>hRegular a r hSupport hZero.
have [q [t [hDivision hUnique]]]:=@weierstrass_division_with_transverse R X K NX NK hNX hNK
  v xi inclusion projection n (J H) 0 hSplit hXi hRegular.
have hRemainder:=@analytic_polynomial_support_directional_remainder R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embed variable coefficient hP J hJ r n hXiValues hSupport.
have hCandidate:@is_weierstrass_division R X NX hNX n v (J H) 0 a (J r).
  constructor;[exact:hZero|exact:hRemainder].
have hZeroSupport:forall i,(n<=i)%N ->coefficient 0 i = 0.
  move=>i _;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
have hZeroRemainder:=@analytic_polynomial_support_directional_remainder R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embed variable coefficient hP J hJ 0 n hXiValues hZeroSupport.
rewrite rmorph0 in hZeroRemainder.
have hZeroCandidate:@is_weierstrass_division R X NX hNX n v (J H) 0 0 0.
  constructor;first by rewrite mul0r addr0.
  exact:hZeroRemainder.
have hT:=(hUnique a (J r) hCandidate).2.
have hZeroT:=(hUnique 0 0 hZeroCandidate).2.
have hImageZero:J r = 0 by rewrite hT -hZeroT.
have hInjective:=@analytic_transverse_polynomial_evaluation_injective R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embed variable coefficient hP J hJ hXiValues.
apply:hInjective;by rewrite hImageZero rmorph0.
Qed.
End ActualDivision.
