(** Federer (1969), 2.9.19, p. 164: the derivative of g is obtained from
    those of s and s-g. These elementary limit consequences use only the
    preceding epsilon specification, without importing a calculus module. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [punctured_real_limit_congr]: supporting replacement of equal
    nonzero-increment expressions in Federer 2.9.19, p. 164 Values at
    increment zero have no bearing on the derivative limit. *)
Lemma punctured_real_limit_congr (R : realType) (u v : R -> R) (a : R) :
  (forall h, h != 0 -> u h=v h) ->
  punctured_real_limit u a -> punctured_real_limit v a.
Proof.
move=> huv hu e he; have [d [hd hb]] := hu e he.
exists d; split=> // h /andP [hh hhd].
have hn : h != 0 by move: hh; rewrite normr_gt0.
rewrite -(huv h hn); apply: hb; by apply/andP; split.
Qed.

(** Source for [punctured_real_limit_subtract]: supporting finite limit
    subtraction in Federer 2.9.19, p. 164 A common radius cutoff and two
    half-epsilon estimates prove the limit for all sufficiently small
    nonzero increments. *)
Lemma punctured_real_limit_subtract (R : realType) (u v : R -> R) (a b : R) :
  punctured_real_limit u a -> punctured_real_limit v b ->
  punctured_real_limit (fun h => u h-v h) (a-b).
Proof.
move=> hu hv e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [du [hdu hU]] := hu (e/2) he2.
have [dv [hdv hV]] := hv (e/2) he2.
exists (Num.min du dv); split; first by rewrite lt_min hdu hdv.
move=> h /andP [hh hhd].
have hminu : Num.min du dv<=du by rewrite ge_min lexx.
have hminv : Num.min du dv<=dv by rewrite ge_min lexx orbT.
have hdu' : `|h|<du := lt_le_trans hhd hminu.
have hdv' : `|h|<dv := lt_le_trans hhd hminv.
have hu' := hU h (ltac:(by apply/andP; split)).
have hv' := hV h (ltac:(by apply/andP; split)).
have heq : (u h-v h)-(a-b)=(u h-a)-(v h-b) by ring.
rewrite heq; apply: le_lt_trans (ler_normB _ _) _.
have hh' := ltrD hu' hv'.
have heq' : e/2+e/2=e by lra.
by rewrite heq' in hh'.
Qed.

(** Source for [has_real_curve_derivative_subtract]: direct subtraction step
    g'=s'-(s-g)' in Federer 2.9.19, p. 164, formulated for arbitrary
    differentiable real functions. This derives the new derivative from the
    limit laws; differentiability is not an assumed calculus rule. *)
Lemma has_real_curve_derivative_subtract (R : realType) (f g : R -> R) (x a b : R) :
  has_real_curve_derivative f x a -> has_real_curve_derivative g x b ->
  has_real_curve_derivative (fun t => f t-g t) x (a-b).
Proof.
move=> hf hg; apply: (@punctured_real_limit_congr R
  (fun h => (f (x+h)-f x)/h-(g (x+h)-g x)/h)).
- by move=> h _; ring.
- exact: punctured_real_limit_subtract hf hg.
Qed.
