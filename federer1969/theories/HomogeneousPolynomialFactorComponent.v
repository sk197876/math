(** Federer (1969), 3.4.5, p. 321: homogeneous
    polynomial divisibility in the real Taylor argument
    for the cited analytic counterexample. Only one
    original homogeneous quotient component is needed. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom SymmetricForms SymmetricFormSum HomogeneousPolynomialFunctions
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor PolynomialTaylorExactExpansion
  PolynomialCoefficientUniqueness FiniteHornerCoefficientEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_factor_component]:
    if p and H are homogeneous of degrees d and
    k and p=QH, the degree d-k component of the
    actual polynomial Q gives the entire product. If
    d<k, p is zero. This supports 3.4.5, p. 321. *)
Theorem homogeneous_polynomial_factor_component (R:realType) (X:lmodType R)
    d k (Q:PolynomialFunction X R^o) (p H:X->R):
  (forall t x,p (t*:x)=t^+d* p x) ->
  (forall t x,H (t*:x)=t^+k*H x) ->
  (forall x,p x=Q x*H x) ->
  forall x,p x=if (d<k)%N then 0 else
    sform_polynomial_value (sform_component (d-k)%N (polynomial_to_forms Q)) x*H x.
Proof.
move=>hPScale hHScale hFactor x.
pose j:=(d-k)%N.
pose L:=maxn (polynomial_degree Q) j.
pose N:=L.+1.
pose b:=[seq sform_polynomial_value (sform_component m (polynomial_to_forms Q)) x*H x|
  m<-iota 0 N].
have hOrder:(polynomial_degree Q<=L)%N:=leq_maxl _ _.
have hQValue (t:R):Q (t*:x)=\sum_(m<N)
    t^+m*sform_polynomial_value (sform_component m (polynomial_to_forms Q)) x.
  have hTaylor:=@polynomial_taylor_formula_any_higher_order R (@pchar_num R) X R^o
    Q L 0 (t*:x) hOrder.
  rewrite add0r in hTaylor;rewrite hTaylor.
  apply:eq_bigr=>m _.
  by rewrite (polynomial_taylor_coefficient_at_zero (@pchar_num R)) sform_polynomial_scale_argument.
have hBValue (t:R):@coefficient_polynomial_value R R^o b t=
    \sum_(m<N) t^+m*(sform_polynomial_value (sform_component m (polynomial_to_forms Q)) x*H x).
  rewrite coefficient_polynomial_sum /b size_map size_iota.
  apply:eq_bigr=>m _.
  by rewrite (nth_map 0) ?size_iota ?ltn_ord // nth_iota ?ltn_ord // add0n.
have hShift (t:R):t^+d* p x=t^+k*@coefficient_polynomial_value R R^o b t.
  rewrite -(hPScale t x) hFactor hHScale hQValue hBValue mulr_suml mulr_sumr.
  apply:eq_bigr=>m _;ring.
have hCoefficient:=@finite_monomial_shift_coefficient R d k (p x) b hShift.
case hLess:(d<k)%N;rewrite hLess in hCoefficient *;first exact:hCoefficient.
have hJBound:(j<N)%N by rewrite /N /L ltnS leq_maxr.
rewrite /b (nth_map 0) ?size_iota ?hJBound // nth_iota ?hJBound // add0n in hCoefficient.
Qed.
