(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: actual bounded coefficient images give the
    increasing ideals used in Hilbert's theorem. Source:
    Bourbaki, Commutative Algebra (1972), Chapter III,
    section 2, no. 10, Corollary 1, p. 184. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativePolynomialUP
  CommutativePolynomialBasicLaws PolynomialCoefficientDivision PolynomialTruncatedLeadingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [truncated_polynomial_leading_family_exists]:
    the bounded coefficient-image specification has an actual
    witness, supporting the coefficient proof of Hilbert's
    theorem; Bourbaki (1972), Chapter III, section 2,
    no. 10, Corollary 1, p. 184. *)
Theorem truncated_polynomial_leading_family_exists (A B:comNzRingType)
    (coefficient:B->nat->A) (I:set B):
  exists L:nat->set A,is_truncated_polynomial_leading_family coefficient I L.
Proof.
exists (fun d a=>exists P:B,I P /\
  (forall i,(d<i)%N ->coefficient P i = 0) /\coefficient P d = a).
by move=>d a.
Qed.

Section LeadingIdeals.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable I:set B.
Hypothesis hI:is_commutative_ideal I.
Variable L:nat->set A.
Hypothesis hL:is_truncated_polynomial_leading_family coefficient I L.

(** Source for [truncated_polynomial_leading_is_ideal]:
    each bounded leading-coefficient image is an ideal;
    the coefficient proof of Hilbert's theorem, Bourbaki
    (1972), Chapter III, section 2, no. 10,
    Corollary 1, p. 184, supporting 3.4.8(5), p. 328. *)
Lemma truncated_polynomial_leading_is_ideal d:is_commutative_ideal (L d).
Proof.
constructor.
- apply/(hL d 0);exists 0;split;first exact:commutative_ideal_zero hI.
  split;first by move=>i _;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
  exact:(@polynomial_coefficient_zero A B embed variable coefficient hP d).
- move=>a b /(hL d a)[P [hIP [hPHigh hPCoeff]]]
    /(hL d b)[Q [hIQ [hQHigh hQCoeff]]].
  apply/(hL d (a+b));exists (P+Q);split;first exact:(@commutative_ideal_add B I hI P Q hIP hIQ).
  split.
  + move=>i hi;by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP)
      hPHigh // hQHigh // addr0.
  + by rewrite (@polynomial_coefficient_add A B embed variable coefficient hP) hPCoeff hQCoeff.
- move=>a /(hL d a)[P [hIP [hPHigh hPCoeff]]].
  apply/(hL d (-a));exists (-P);split;first exact:(@commutative_ideal_opp B I hI P hIP).
  split.
  + move=>i hi;by rewrite (@polynomial_coefficient_opp A B embed variable coefficient hP) hPHigh // oppr0.
  + by rewrite (@polynomial_coefficient_opp A B embed variable coefficient hP) hPCoeff.
- move=>a b /(hL d b)[P [hIP [hPHigh hPCoeff]]].
  apply/(hL d (a*b));exists (embed a*P);split.
  + exact:(@commutative_ideal_mul B I hI (embed a) P hIP).
  + split.
    * move=>i hi;by rewrite (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP)
        hPHigh // mulr0.
    * by rewrite (@polynomial_coefficient_scalar_multiply A B embed variable coefficient hP) hPCoeff.
Qed.

(** Source for [truncated_polynomial_leading_successor]:
    multiplication by the original variable gives the next
    bounded coefficient ideal, supporting Hilbert's theorem;
    Bourbaki (1972), Chapter III, section 2, no. 10,
    Corollary 1, p. 184, for the algebra of 3.4.8(5), p. 328. *)
Lemma truncated_polynomial_leading_successor d:L d `<=` L d.+1.
Proof.
move=>a /(hL d a)[P [hIP [hHigh hCoefficient]]].
apply/(hL d.+1 a);exists (variable*P);split.
- exact:(@commutative_ideal_mul B I hI variable P hIP).
- split.
  + move=>[|i] hi;first by [].
    rewrite (@polynomial_variable_multiply_coefficient A B embed variable coefficient hP) /= subSS subn0.
    exact:hHigh i hi.
  + by rewrite (@polynomial_variable_multiply_coefficient A B embed variable coefficient hP) /= subSS subn0.
Qed.

(** Source for [truncated_polynomial_leading_monotone]:
    bounded coefficient ideals form an increasing family,
    the chain used in Hilbert's theorem; Bourbaki (1972),
    Chapter III, section 2, no. 10, Corollary 1, p. 184,
    supporting the algebra for 3.4.8(5), p. 328. *)
Lemma truncated_polynomial_leading_monotone i j:
  (i<=j)%N ->L i `<=` L j.
Proof.
elim:j=>[|j ih] hij.
- have /eqP hZero:i==0%N by rewrite -leqn0.
  subst i;by move=>a ha.
- move:hij;rewrite leq_eqVlt;move/orP=>[/eqP ->|hij];first by move=>a ha.
  move=>a ha;exact:(@truncated_polynomial_leading_successor j a (ih hij a ha)).
Qed.
End LeadingIdeals.
