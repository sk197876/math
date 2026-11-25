(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: the independent monic relation
    gives an actual nonzero annihilating polynomial.
    Apply the existing finite coefficient-expression and
    evaluation laws. Source: Bourbaki, Algebra II
    (1990), Chapter V, section 3, no. 1,
    Theorem 1, pp. V.16–17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialFiniteSums CommutativePolynomialDegreeBounds CommutativePolynomialMonicUP
  CommutativePolynomialEvaluationUP IntegralRingElementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [integral_ring_element_monic_annihilator]:
    the original integral relation is represented by
    a monic polynomial of positive degree, as
    in the cited minimal-polynomial definition, p. V.16,
    supporting the integral extension in 3.4.8(8),
    p. 329. No polynomial representation is assumed. *)
Theorem integral_ring_element_monic_annihilator (A B C:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (x:C) (E:{rmorphism B->C}):
  is_commutative_polynomial_evaluation embed variable phi x E ->
  is_integral_ring_element phi x ->exists (H:B) k,
    is_monic_polynomial coefficient H k /\(0<k)%N /\E H = 0.
Proof.
move=>hE [k [c [hPositive hRelation]]].
pose Q:=\sum_(i<k) embed (c i)*variable^+(i:nat).
pose H:=variable^+k-Q.
have hCoefficient i:coefficient H i =
    (if i==k then 1 else 0)-(if (i<k)%N then c i else 0).
  rewrite /H /Q (@polynomial_subtract_coefficients A B embed variable coefficient hP)
    (@polynomial_power_coefficient A B embed variable coefficient hP).
  by rewrite (@polynomial_finite_expression_coefficient A B embed variable coefficient hP).
have hMonic:coefficient H k = 1 by rewrite hCoefficient eqxx ltnn subr0.
have hDegree:is_monic_polynomial coefficient H k.
  split;last exact:hMonic.
  split.
  - rewrite hMonic;by apply/eqP;exact:oner_neq0.
  - move=>i hi.
    have hIK:(i==k) = false.
      apply/negP=>/eqP h;by rewrite h ltnn in hi.
    by rewrite hCoefficient hIK (leq_gtF (ltnW hi)) subrr.
have hQ:E Q = \sum_(i<k) phi (c i)*x^+(i:nat).
  rewrite /Q rmorph_sum;apply:eq_bigr=>i _.
  by rewrite rmorphM rmorphXn (polynomial_evaluation_constants hE) (polynomial_evaluation_variable hE).
exists H,k;split;first exact:hDegree.
split;first exact:hPositive.
by rewrite /H rmorphB rmorphXn (polynomial_evaluation_variable hE) hQ hRelation subrr.
Qed.
