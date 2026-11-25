(** Federer (1969), 3.1.24, pp. 240–241: the
    absolute sums in the coordinate Taylor series are bounded
    by a scalar geometric series in positive degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal ring.
From Federer Require Import RealNormUP SymmetricForms SymmetricMultiIndices SymmetricIndexBounds
  SymmetricDividedMonomials SymmetricMonomialTuples SymmetricOperatorNorm
  PolynomialWeightedNormBound ScalarDividedMultinomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_coordinate_degree_majorant]: the
    degree-m contribution to the absolute sum in Federer
    3.1.24, p. 241. Applying 1.10.5 to a unit-norm
    coordinate family and a form bounded by c^m m! gives
    (c sum |t_i|)^m. In the analytic application m is
    positive; the constant term requires its own value bound. *)
Lemma analytic_coordinate_degree_majorant (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) n
    (v:'I_n->X) (hv:forall i,NX (v i)<=1) (t:'I_n->R) m (phi:S_m X Y m) c :
  (symmetric_operator_norm hNX.1 NY phi<=(c^+m*(m`!)%:R)%:E)%E ->
  \sum_(a:symmetric_indices n m)
    `|symmetric_scalar_monomial t (symmetric_indices_unbound a)/
      (symmetric_multi_factorial (symmetric_indices_unbound a))%:R|*
    NY (phi (symmetric_monomial_tuple v a))<=(c*\sum_i `|t i|)^+m.
Proof.
move=>hb.
have hS:0<=\sum_i `|t i| by apply:sumr_ge0=>i _; exact: normr_ge0.
have hfac:0<((m`!)%:R:R) by rewrite ltr0n fact_gt0.
have hweight:0<=(\sum_i `|t i|)^+m/(m`!)%:R.
  exact (divr_ge0 (exprn_ge0 m hS) (ltW hfac)).
have hh:=@homogeneous_polynomial_coefficient_operator_bound R X Y NX NY hNX.1 n v hv t m phi.
have hw:(0<=((\sum_i `|t i|)^+m/(m`!)%:R)%:E)%E by rewrite lee_fin.
have hmul:=lee_wpmul2r hw hb.
have htotal:=le_trans hh hmul.
rewrite -EFinM lee_fin in htotal.
have he:(c^+m*(m`!)%:R)*((\sum_i `|t i|)^+m/(m`!)%:R)=
    (c*\sum_i `|t i|)^+m.
  rewrite exprMn; by field; rewrite gt_eqF.
by rewrite he in htotal.
Qed.

(** Source for [analytic_coordinate_zero_degree_cost]: the
    constant term of the absolute coordinate sum in Federer
    3.1.24, p. 241, has its actual value's norm.
    It is not bounded by one by condition (1), which concerns
    positive orders only. The scalar degree-zero multinomial
    identity also covers an empty coordinate family. *)
Lemma analytic_coordinate_zero_degree_cost (R:realType) (X Y:lmodType R)
    (NY:Y->R) n (v:'I_n->X) (t:'I_n->R) (phi:S_m X Y 0) :
  \sum_(a:symmetric_indices n 0)
    `|symmetric_scalar_monomial t (symmetric_indices_unbound a)/
      (symmetric_multi_factorial (symmetric_indices_unbound a))%:R|*
    NY (phi (symmetric_monomial_tuple v a))=
  NY (phi [tuple (0:X) | i<0]).
Proof.
have ht (a:symmetric_indices n 0):symmetric_monomial_tuple v a= [tuple (0:X) | i<0].
  apply: eq_from_tnth=>i; by have:=valP i; rewrite ltn0.
under eq_bigr do rewrite ht.
rewrite -big_distrl scalar_divided_multinomial_absolute expr0 fact0 divr1 ?mul1r ?mulr1.
change ((1:R)*NY (phi [tuple (0:X) | i<0])=NY (phi [tuple (0:X) | i<0])).
by rewrite mul1r.
Qed.
