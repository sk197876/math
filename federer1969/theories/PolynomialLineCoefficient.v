(** Federer (1969), 3.1.11, p. 222: comparing scalar
    powers in the polynomial composition identifies each homogeneous
    Taylor coefficient. The coefficient uniqueness is proved in 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricForms HomogeneousPolynomialFunctions
  PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  PolynomialCoefficientUniqueness PolynomialTaylorExactExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_line_expansion_coefficient]: the
    coefficient of t^p in P(a+t v) is the divided-power value
    of its pth Taylor form, supporting the last equality in
    Federer 3.1.11, p. 222. No bound on the full degree
    of P is an additional hypothesis. *)
Theorem polynomial_line_expansion_coefficient (K : fieldType)
    (h0 : [pchar K]=i pred0) (X Y : lmodType K)
    (P : PolynomialFunction X Y) a v M (c : nat->Y) :
  (forall t, P (a+t*:v)=\sum_(j<M) t^+j*:c j) ->
  forall i, (i<M)%N ->
    sform_polynomial_value (polynomial_taylor_coefficient P i a) v=c i.
Proof.
move=>hP i hi.
pose L := maxn M (polynomial_degree P).
have hML : (M<=L)%N := leq_maxl _ _.
have hdL : (polynomial_degree P<=L)%N := leq_maxr _ _.
have hMN : (M<=L.+1)%N := leq_trans hML (leqnSn L).
pose d j := sform_polynomial_value (polynomial_taylor_coefficient P j a) v.
pose b j := if (j<M)%N then c j else 0.
have hd t : P (a+t*:v)=\sum_(j<L.+1) t^+j*:d j.
  rewrite (@polynomial_taylor_formula_any_higher_order K h0 X Y P L a (t*:v) hdL).
  apply: eq_bigr=>j _; exact: sform_polynomial_scale_argument.
have hb t : P (a+t*:v)=\sum_(j<L.+1) t^+j*:b j.
  rewrite hP (big_ord_widen L.+1 (fun j=>t^+j*:c j) hMN) big_mkcond.
  apply: eq_bigr=>j _; rewrite /b; by case:(j<M)%N; rewrite ?scaler0.
have hz t : \sum_(j<L.+1) t^+j*:(d j-b j)=0.
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -hd -hb subrr.
have hiL : (i<L.+1)%N := leq_trans hi hMN.
have hh := @finite_power_coefficients_zero K h0 Y L.+1 (fun j=>d j-b j) hz i hiL.
move/eqP:hh; by rewrite subr_eq0 /b hi=>/eqP.
Qed.
