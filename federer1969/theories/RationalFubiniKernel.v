(** Federer (1969), 2.6.3(2), pp. 117–118: the rational kernel on the
    positive quadrant and the two displayed primitive expressions. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rational_fubini_density]: the rational
    expression (4xy-x^2-y^2)/(x+y)^4 in Federer
    2.6.3(2), p. 117, before restriction to the
    positive quadrant. It is only used where its denominator
    is nonzero in the integral computations. *)
Definition rational_fubini_density (R : realType) (x y : R) : R :=
  (4*x*y-x^+2-y^+2)/(x+y)^+4.

(** Source for [rational_fubini_kernel]: the exact piecewise function f of
    Federer 2.6.3(2), p. 117 It vanishes whenever either coordinate is
    nonpositive. *)
Definition rational_fubini_kernel (R : realType) (x y : R) : R :=
  if (0 < x) && (0 < y) then rational_fubini_density x y else 0.

(** Source for [rational_first_primitive]: the right side of the first
    displayed integral evaluation in Federer 2.6.3(2), p. 117 *)
Definition rational_first_primitive (R : realType) (y x : R) : R :=
  (x^+2-x*y)/(x+y)^+3.

(** Source for [rational_second_primitive]: supporting primitive a*y/(a+y)^2
    for the second integral calculation in Federer 2.6.3(2), p. 118 At y=m*a
    its value is the printed a^2*m/(a+m*a)^2. *)
Definition rational_second_primitive (R : realType) (a y : R) : R :=
  a*y/(a+y)^+2.

(** Source for [rational_fubini_kernel_positive]: agreement
    with the displayed rational expression in the positive
    quadrant, Federer 2.6.3(2), p. 117. *)
Lemma rational_fubini_kernel_positive (R : realType) (x y : R) :
  0 < x -> 0 < y -> rational_fubini_kernel x y = rational_fubini_density x y.
Proof. by move=> hx hy; rewrite /rational_fubini_kernel hx hy. Qed.

(** Source for [rational_fubini_kernel_nonpositive_left]:
    the prescribed zero value on the nonpositive first
    half-plane, Federer 2.6.3(2), p. 117. *)
Lemma rational_fubini_kernel_nonpositive_left (R : realType) (x y : R) :
  x <= 0 -> rational_fubini_kernel x y=0.
Proof. by move=> hx; rewrite /rational_fubini_kernel ltNge hx. Qed.

(** Source for [rational_fubini_kernel_nonpositive_right]:
    the prescribed zero value on the nonpositive second
    half-plane, Federer 2.6.3(2), p. 117. *)
Lemma rational_fubini_kernel_nonpositive_right (R : realType) (x y : R) :
  y <= 0 -> rational_fubini_kernel x y=0.
Proof. by move=> hy; rewrite /rational_fubini_kernel [0 < y]ltNge hy andbF. Qed.

(** Source for [rational_fubini_kernel_symmetric]: symmetry used to obtain
    the second iterated integral in Federer 2.6.3(2), p. 118 *)
Lemma rational_fubini_kernel_symmetric (R : realType) (x y : R) :
  rational_fubini_kernel x y = rational_fubini_kernel y x.
Proof.
rewrite /rational_fubini_kernel [(_ < y) && _]andbC.
case: ifP=> _ //; rewrite /rational_fubini_density [y+x]addrC.
congr (_ / _); ring.
Qed.

(** Source for [rational_first_primitive_zero]: vanishing
    lower endpoint in the first integral evaluation of
    Federer 2.6.3(2), p. 117. *)
Lemma rational_first_primitive_zero (R : realType) (y : R) : rational_first_primitive y 0=0.
Proof. by rewrite /rational_first_primitive expr0n mul0r subr0 mul0r. Qed.

(** Source for [rational_second_primitive_zero]: vanishing
    lower endpoint in the second integral evaluation of
    Federer 2.6.3(2), p. 118. *)
Lemma rational_second_primitive_zero (R : realType) (a : R) : rational_second_primitive a 0=0.
Proof. by rewrite /rational_second_primitive mulr0 mul0r. Qed.

(** Source for [rational_second_primitive_scaled_endpoint]: the final
    m/(1+m)^2 value in Federer 2.6.3(2), p. 118 This algebraic identity is
    independent of the scale a>0. *)
Lemma rational_second_primitive_scaled_endpoint (R : realType) (a m : R) :
  0 < a -> 0 < m -> rational_second_primitive a (m*a)=m/(1+m)^+2.
Proof.
move=> ha hm; have ha0 := gt_eqF ha; have hmpos : 0 < 1+m by lra.
have hm0 : 1+m != 0 by rewrite (gt_eqF hmpos).
have hsum : a+m*a=a*(1+m) by ring.
rewrite /rational_second_primitive hsum; by field; rewrite ha0 hm0.
Qed.
