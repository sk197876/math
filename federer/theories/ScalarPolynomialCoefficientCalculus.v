(** Federer (1969), 3.1.11, p. 223:
    finite coefficient algebra for the derivatives
    of P(1/x) exp(-x^-2). Coefficient lists
    use the project's Horner evaluation from
    1.10.4, p. 46; no external polynomial
    or differentiation library is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import PolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_polynomial_coefficient_add]:
    addition of finite polynomial coefficients,
    supporting the flat-function derivative computation
    in Federer 3.1.11, p. 223. *)
Fixpoint scalar_polynomial_coefficient_add (K : fieldType)
    (s t : seq K) : seq K :=
  match s,t with
  | a::s',b::t'=>a+b::scalar_polynomial_coefficient_add s' t'
  | [::],_=>t
  | _,[::]=>s
  end.

(** Source for [scalar_polynomial_coefficient_add_value]:
    coefficient addition gives pointwise polynomial
    addition, used in the derivative recursion
    for Federer 3.1.11, p. 223. *)
Lemma scalar_polynomial_coefficient_add_value (K : fieldType) (s t : seq K) x :
  @coefficient_polynomial_value K K^o (scalar_polynomial_coefficient_add s t) x=
    @coefficient_polynomial_value K K^o s x+@coefficient_polynomial_value K K^o t x.
Proof.
elim: s t=>[|a s ih] t.
- change (@coefficient_polynomial_value K K^o t x=
    0+@coefficient_polynomial_value K K^o t x).
  by rewrite add0r.
- case: t=>[|b t].
  + change (@coefficient_polynomial_value K K^o (a::s) x=
      @coefficient_polynomial_value K K^o (a::s) x+0).
    by rewrite addr0.
  + change (a+b+x* @coefficient_polynomial_value K K^o (scalar_polynomial_coefficient_add s t) x=
      (a+x* @coefficient_polynomial_value K K^o s x)+(b+x* @coefficient_polynomial_value K K^o t x)).
    by rewrite ih mulrDr addrACA.
Qed.

(** Source for [scalar_polynomial_coefficient_scale_value]:
    multiplying every coefficient scales the polynomial,
    supporting the derivative recursion in Federer
    3.1.11, p. 223. *)
Lemma scalar_polynomial_coefficient_scale_value (K : fieldType) (c : K) s x :
  @coefficient_polynomial_value K K^o [seq c*a | a<-s] x=
    c*@coefficient_polynomial_value K K^o s x.
Proof.
elim: s=>[|a s ih].
- by rewrite /coefficient_polynomial_value /= mulr0.
- change (c*a+x*@coefficient_polynomial_value K K^o [seq c*b | b<-s] x=
    c*(a+x*@coefficient_polynomial_value K K^o s x)).
  by rewrite ih mulrDr !mulrA [x*c]mulrC.
Qed.

(** Source for [scalar_polynomial_coefficient_shift_value]:
    prefixing n zero coefficients multiplies by x^n,
    supporting the factors z^2 and z^3 in
    the flat-function derivative of Federer
    3.1.11, p. 223. *)
Lemma scalar_polynomial_coefficient_shift_value (K : fieldType) n s x :
  @coefficient_polynomial_value K K^o (nseq n 0++s) x=
    x^+n*@coefficient_polynomial_value K K^o s x.
Proof.
elim: n=>[|n ih].
- by rewrite /= expr0 mul1r.
- change (0+x*@coefficient_polynomial_value K K^o (nseq n 0++s) x=
    x^+n.+1*@coefficient_polynomial_value K K^o s x).
  by rewrite add0r ih exprS mulrA.
Qed.

(** Source for [scalar_polynomial_derivative_coefficients]:
    finite differentiation of a scalar polynomial,
    used only as coefficient arithmetic for the
    smooth example in Federer 3.1.11, p. 223.
    The derivative law is proved separately. *)
Fixpoint scalar_polynomial_derivative_coefficients (K : fieldType) (s : seq K) :=
  if s is c::t then scalar_polynomial_coefficient_add t
    (0::scalar_polynomial_derivative_coefficients t)
  else [::].

(** Source for [scalar_polynomial_derivative_step]:
    the formal derivative of c+x P(x)
    is P(x)+x P'(x), supporting Federer
    3.1.11, p. 223. *)
Lemma scalar_polynomial_derivative_step (K : fieldType) (c : K) s x :
  @coefficient_polynomial_value K K^o (scalar_polynomial_derivative_coefficients (c::s)) x=
    @coefficient_polynomial_value K K^o s x+
      x*@coefficient_polynomial_value K K^o (scalar_polynomial_derivative_coefficients s) x.
Proof.
rewrite /= scalar_polynomial_coefficient_add_value.
by rewrite /coefficient_polynomial_value /= add0r.
Qed.

(** Source for [flat_exponential_polynomial_step]:
    the coefficient polynomial changes from P(z)
    to -z^2 P'(z)+2z^3 P(z) when
    differentiating P(1/x) exp(-x^-2), in
    Federer 3.1.11, p. 223. *)
Definition flat_exponential_polynomial_step (K : fieldType) (s : seq K) :=
  scalar_polynomial_coefficient_add
    [seq -a | a<-nseq 2 0++scalar_polynomial_derivative_coefficients s]
    [seq 2*a | a<-nseq 3 0++s].

(** Source for [flat_exponential_polynomial_step_value]:
    evaluation of the finite coefficient update
    gives -z^2 P'(z)+2z^3 P(z), the
    recurrence used in Federer 3.1.11, p. 223. *)
Lemma flat_exponential_polynomial_step_value (K : fieldType) (s : seq K) z :
  @coefficient_polynomial_value K K^o (flat_exponential_polynomial_step s) z=
    -(z^+2)*@coefficient_polynomial_value K K^o (scalar_polynomial_derivative_coefficients s) z+
    2*z^+3*@coefficient_polynomial_value K K^o s z.
Proof.
rewrite /flat_exponential_polynomial_step scalar_polynomial_coefficient_add_value.
have he t : [seq -a | a<-t]=[seq (-1)*a | a<-t].
  by apply: eq_map=>a; rewrite mulN1r.
rewrite he !scalar_polynomial_coefficient_scale_value
  !scalar_polynomial_coefficient_shift_value.
by rewrite !mulrA mulN1r expr2 !mulNr.
Qed.
