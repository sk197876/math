(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: the first d powers of
    an original primitive element form a basis.
    Reuse the minimal kernel, bounded-divisibility,
    monic reduction and finite-basis criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeDomainUP CommutativePolynomialUP
  CommutativePolynomialBasicLaws CommutativePolynomialFiniteSums
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws
  PolynomialMonicPrimeBounds FieldPolynomialMinimumUP PolynomialMonicEvaluationImage
  RingScalarRestriction LinearBasis FiniteIndependence FiniteSpans FiniteBasisCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [minimal_polynomial_power_basis]: the
    power basis of a simple algebraic extension,
    supporting the simplicity assertion invoked in
    3.4.8(8), p. 330; Bourbaki (1990), Chapter V,
    section 3, no. 1, Theorem 1,
    pp. V.16–17. The original evaluation image
    is the whole extension, and the exact
    minimal kernel proves linear independence. *)
Theorem minimal_polynomial_power_basis (K L:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}) (x:L) (E:{rmorphism B->L}) (H:B) d:
  is_commutative_polynomial_evaluation embed variable phi x E ->
  is_minimal_field_polynomial coefficient E H d ->(forall y:L,exists P:B,E P = y) ->
  @is_basis K (Choice.clone 'I_d _)
    [the lmodType K of ring_restricted_space phi L^o] (fun i:'I_d=>x^+(i:nat)).
Proof.
move=>hE hH hOnto.
have hDomain:is_commutative_integral_domain K.
  move=>a b /eqP;rewrite mulf_eq0;move/orP=>[/eqP hA|/eqP hB];[by left|by right].
have hDegree:=(minimal_field_polynomial_monic hH).1.
have hMonic:=(minimal_field_polynomial_monic hH).2.
have hZero:=minimal_field_polynomial_vanishes hH.
apply:finite_basis_criterion.
- move=>c hSum i.
  pose P:=\sum_(j<d) embed (c j)*variable^+(j:nat).
  have hCoefficient k:coefficient P k = \sum_(j<d) (if k==(j:nat) then c j else 0).
    rewrite /P (@polynomial_coefficient_sum K B embed variable coefficient hP).
    apply:eq_bigr=>j _;exact:(@polynomial_monomial_coefficient K B embed variable coefficient hP (c j) (j:nat) k).
  have hBound k (hK:(d<=k)%N):coefficient P k = 0.
    rewrite hCoefficient;apply:big1=>j _.
    have hDifferent:(k==(j:nat)) = false.
      apply/negP=>/eqP hSame;have hJ:=ltn_ord j.
      by rewrite -hSame (leq_gtF hK) in hJ.
    by rewrite hDifferent.
  have hEvaluation:E P = 0.
    rewrite /P rmorph_sum.
    under eq_bigr do rewrite rmorphM rmorphXn (polynomial_evaluation_constants hE)
      (polynomial_evaluation_variable hE).
    exact:hSum.
  have hPZero:=@polynomial_bounded_divisible_zero K B embed variable coefficient hP hDomain H P d
    hDegree hBound ((minimal_field_polynomial_kernel hH P).1 hEvaluation).
  have hAt:coefficient P (i:nat) = c i.
    rewrite hCoefficient (bigD1 i) //= eqxx.
    have hOthers:(\sum_(j<d|j!=i) (if (i:nat)==(j:nat) then c j else 0)) = 0.
      apply:big1=>j hJI.
      have hDifferent:((i:nat)==(j:nat)) = false.
        apply/negP=>/eqP hSame.
        have hIJ:i = j:=val_inj hSame.
        by rewrite hIJ eqxx in hJI.
      by rewrite hDifferent.
    by rewrite hOthers addr0.
  rewrite -hAt hPZero;exact:(@polynomial_coefficient_zero K B embed variable coefficient hP (i:nat)).
- move=>y;have [P hPY]:=hOnto y.
  have hImage:exists P:B,y = E P by exists P;exact:esym hPY.
  have [r [hBound hValue]]:=(@monic_polynomial_evaluation_bounded_image K B L embed variable coefficient
    hP hDomain E H d hDegree hMonic hZero y).1 hImage.
  exists (fun i:'I_d=>coefficient r (i:nat)).
  change (y = \sum_(i<d) phi (coefficient r (i:nat))*x^+(i:nat)).
  rewrite hValue;exact:(@polynomial_evaluation_finite_expression K B L embed variable coefficient hP phi x E hE r d hBound).
Qed.
