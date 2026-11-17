(** Federer (1969), 3.4.7, p. 325: private
    finite-expression witness for polynomial evaluation. The
    independently specified extension equations will hide the
    support bound and its finite-sum representation. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP FinitePrefixSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Witness.
Variables A B C:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable phi:{rmorphism A->C}.
Variable t:C.

(** Source for [polynomial_substitution_bound]: a local
    choice of finite support bound for the existence
    witness, supporting 3.4.7, p. 325. *)
Definition polynomial_substitution_bound (P:B):nat:=
  projT1 (cid (@polynomial_coefficients_finite A B embed variable coefficient hP P)).

(** Source for [polynomial_substitution_support]: the chosen
    bound is an actual support bound, supporting
    substitution in 3.4.7, p. 325. *)
Lemma polynomial_substitution_support (P:B):
  forall i,(polynomial_substitution_bound P<=i)%N ->coefficient P i = 0.
Proof. exact:(projT2 (cid (@polynomial_coefficients_finite A B embed variable coefficient hP P))). Qed.

(** Source for [polynomial_substitution_witness]: the actual
    finite expression at the chosen ring element,
    supporting evaluation in 3.4.7, p. 325. *)
Definition polynomial_substitution_witness (P:B):C:=
  \sum_(i<polynomial_substitution_bound P) phi (coefficient P i)*t^+i.

(** Source for [polynomial_substitution_any_bound]: any actual
    support bound gives the same evaluation, supporting
    the construction independence in 3.4.7, p. 325. *)
Lemma polynomial_substitution_any_bound (P:B) N:
  (forall i,(N<=i)%N ->coefficient P i = 0) ->
  polynomial_substitution_witness P = \sum_(i<N) phi (coefficient P i)*t^+i.
Proof.
move=>hN;rewrite /polynomial_substitution_witness.
apply:(@finite_prefix_sum_support_independent C
  (fun i=>phi (coefficient P i)*t^+i) (polynomial_substitution_bound P) N).
- move=>i hi;by rewrite polynomial_substitution_support // rmorph0 mul0r.
- move=>i hi;by rewrite hN // rmorph0 mul0r.
Qed.

(** Source for [polynomial_substitution_zero]: evaluating
    the zero polynomial gives zero, supporting 3.4.7, p. 325. *)
Lemma polynomial_substitution_zero:polynomial_substitution_witness 0 = 0.
Proof.
have hZero i:(0<=i)%N ->coefficient 0 i = 0.
  move=>_;exact:(@polynomial_coefficient_zero A B embed variable coefficient hP i).
by rewrite (polynomial_substitution_any_bound hZero) big_ord0.
Qed.

(** Source for [polynomial_substitution_constant]: evaluation
    extends the original coefficient map, supporting
    3.4.7, p. 325. *)
Lemma polynomial_substitution_constant (a:A):polynomial_substitution_witness (embed a) = phi a.
Proof.
have hBound i:(1<=i)%N ->coefficient (embed a) i = 0.
  move=>hi;rewrite (@polynomial_coefficient_constant A B embed variable coefficient hP).
  have hDifferent:(i==0%N) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
  by rewrite hDifferent.
rewrite (polynomial_substitution_any_bound hBound) big_ord_recl big_ord0 addr0 /=.
by rewrite (@polynomial_coefficient_constant A B embed variable coefficient hP) /= expr0 mulr1.
Qed.

(** Source for [polynomial_substitution_variable]: the formal
    variable evaluates at the original selected element,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_substitution_variable:polynomial_substitution_witness variable = t.
Proof.
have hBound i:(2<=i)%N ->coefficient variable i = 0.
  move=>hi;rewrite (@polynomial_coefficient_variable A B embed variable coefficient hP).
  have hDifferent:(i==1%N) = false by apply/negP=>/eqP h;by rewrite h ltnn in hi.
  by rewrite hDifferent.
rewrite (polynomial_substitution_any_bound hBound) !big_ord_recl big_ord0 /=.
rewrite !(@polynomial_coefficient_variable A B embed variable coefficient hP) /=
  rmorph0 rmorph1 expr0 expr1 mul0r mul1r add0r addr0.
by [].
Qed.
End Witness.
