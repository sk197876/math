(** Federer (1969), 2.9.19, p. 164: convert interval increment estimates
    into the two-sided difference- quotient limit. These finite arithmetic
    and limit steps use the derivative specification, without an external
    calculus module. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_increment_ratio_error_bound]: supporting division
    step in Federer 2.9.19, p. 164 Bounding an increment between (c-e)r and
    (c+e)r with positive r bounds the quotient error by e. *)
Lemma positive_increment_ratio_error_bound (R : realType) (A r c e : R) :
  0<r -> (c-e)*r<=A -> A<=(c+e)*r -> `|A/r-c|<=e.
Proof.
move=> hr hlo hup.
have hl : c-e<=A/r by rewrite ler_pdivlMr.
have hu : A/r<=c+e by rewrite ler_pdivrMr.
rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [interval_increment_bounds_derivative]: direct final step of
    the monotone proof in Federer 2.9.19, p. 164 Uniform small-interval
    increment estimates around x imply the finite two-sided derivative c.
    For a negative increment, both numerator and denominator are reversed;
    no one-sided derivative is substituted for the conclusion. *)
Lemma interval_increment_bounds_derivative (R : realType) (g : R -> R) (x c : R) :
  (forall e : R, 0<e -> exists d : R, 0<d /\ forall a b : R,
    a<=x<=b -> 0<b-a<d ->
    (c-e)*(b-a)<=g b-g a /\ g b-g a<=(c+e)*(b-a)) ->
  has_real_curve_derivative g x c.
Proof.
move=> hb e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have hhalf : e/2<e by lra.
have [d [hd hB]] := hb (e/2) he2.
exists d; split=> // h /andP [habs hsmall].
case: (ltP 0 h)=> [hh|hh].
- have hhd : h<d by move: hsmall; rewrite (ger0_norm (ltW hh)).
  have haxb : x<=x<=x+h by apply/andP; split; lra.
  have hwidth : 0<(x+h)-x<d by rewrite addrAC subrr add0r; apply/andP; split.
  have [hl hu] := hB x (x+h) haxb hwidth.
  rewrite addrAC subrr add0r in hl hu.
  exact: le_lt_trans (positive_increment_ratio_error_bound hh hl hu) hhalf.
- have hn : h != 0 by move: habs; rewrite normr_gt0.
  have hh' : h<0 by rewrite lt_neqAle hn hh.
  have hneg : 0< -h by rewrite oppr_gt0.
  have hhd : -h<d by move: hsmall; rewrite (ler0_norm hh).
  have haxb : x+h<=x<=x by apply/andP; split; lra.
  have hlen : x-(x+h)= -h by rewrite opprD addrA subrr add0r.
  have hwidth : 0<x-(x+h)<d by rewrite hlen; apply/andP; split.
  have [hl hu] := hB (x+h) x haxb hwidth.
  rewrite hlen in hl hu.
  have herror := positive_increment_ratio_error_bound hneg hl hu.
  have hq : (g (x+h)-g x)/h=(g x-g (x+h))/(-h).
    by symmetry; rewrite -opprB divrNN.
  rewrite hq; exact: le_lt_trans herror hhalf.
Qed.
