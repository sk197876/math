(** Federer (1969), 3.4.7, p. 325: consequences of
    the independent polynomial coefficient laws. These proofs
    do not inspect the finite-support construction. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP NaturalConvolution NaturalConvolutionMonomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Consequences.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_embedding_injective]: constants
    retain their original coefficients, supporting the transcendental
    extension in 3.4.7, p. 325. *)
Lemma polynomial_embedding_injective:injective embed.
Proof.
move=>a b h;have:=congr1 (fun P=>coefficient P 0%N) h.
by rewrite !(@polynomial_coefficient_constant A B embed variable coefficient hP) /=.
Qed.

(** Source for [polynomial_zero_coefficients]: a polynomial
    is zero exactly when every coefficient is zero,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_zero_coefficients (P:B):
  P = 0 <->forall i,coefficient P i = 0.
Proof.
split;first by move=>->;exact:polynomial_coefficient_zero hP.
move=>h;apply:(@polynomial_coefficients_unique A B embed variable coefficient hP)=>i.
by rewrite h (@polynomial_coefficient_zero A B embed variable coefficient hP).
Qed.

(** Source for [polynomial_coefficient_one]: the unit is
    the constant-one expression, supporting 3.4.7, p. 325. *)
Lemma polynomial_coefficient_one i:coefficient 1 i = if i==0%N then 1 else 0.
Proof. rewrite -(@rmorph1 A B embed);exact:(@polynomial_coefficient_constant A B embed variable coefficient hP 1 i). Qed.

(** Source for [polynomial_variable_multiply_coefficient]: multiplying
    by the variable shifts coefficients, supporting 3.4.7, p. 325. *)
Lemma polynomial_variable_multiply_coefficient (P:B) n:
  coefficient (variable*P) n = if (1<=n)%N then coefficient P (n-1)%N else 0.
Proof.
rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
transitivity (natural_coefficient_convolution (fun i=>if i==1%N then 1 else 0) (coefficient P) n).
  rewrite /natural_coefficient_convolution big_mkord;apply:eq_bigr=>i _.
  by rewrite (@polynomial_coefficient_variable A B embed variable coefficient hP).
rewrite natural_convolution_monomial.
by case:(1<=n)%N;rewrite ?mul1r.
Qed.

(** Source for [polynomial_power_coefficient]: powers of
    the variable have one coefficient, supporting the
    simple transcendental extension in 3.4.7, p. 325. *)
Lemma polynomial_power_coefficient d i:
  coefficient (variable^+d) i = if i==d then 1 else 0.
Proof.
elim:d i=>[|d ih] i;first by rewrite expr0 polynomial_coefficient_one.
rewrite exprS polynomial_variable_multiply_coefficient.
case:i=>[|i];first by [].
rewrite /= subSS subn0 ih;by [].
Qed.

(** Source for [polynomial_monomial_coefficient]: a constant
    times a variable power has its single original
    coefficient, supporting 3.4.7, p. 325. *)
Lemma polynomial_monomial_coefficient (a:A) d i:
  coefficient (embed a*variable^+d) i = if i==d then a else 0.
Proof.
rewrite (@polynomial_coefficient_multiply A B embed variable coefficient hP).
transitivity (natural_coefficient_convolution (fun i=>if i==0%N then a else 0) (coefficient (variable^+d)) i).
  rewrite /natural_coefficient_convolution big_mkord;apply:eq_bigr=>j _.
  by rewrite (@polynomial_coefficient_constant A B embed variable coefficient hP).
rewrite natural_convolution_monomial leq0n subn0.
rewrite polynomial_power_coefficient;by case:(i==d);rewrite ?mulr0 ?mulr1.
Qed.
End Consequences.
