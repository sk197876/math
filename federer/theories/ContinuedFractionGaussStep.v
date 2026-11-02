(** Federer (1969), 2.2.9, p. 65: supporting digit extraction for every
    irrational point of (0,1). Bell2016, section 1, p. 1, defines the Gauss
    remainder by the integer part of the reciprocal and notes preservation
    of irrationality. Here only existence of a positive digit and irrational
    remainder is exposed; no choice of an infinite expansion is assumed.
    Source context: ContinuedFractionBranches.v and RationalRealUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint reals.
From Federer Require Import RationalRealUP ContinuedFractionBranches
  ContinuedFractionRationalBranches ContinuedFractionBlocks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [irrational_continued_fraction_step]: supporting
    inverse Gauss step for the classical homeomorphism mentioned
    in Federer 2.2.9, p. 65. Every irrational
    point x in (0,1) has x=1/(a+1+t), with an
    irrational t in (0,1) and natural digit code a. *)
Lemma irrational_continued_fraction_step (R : realType) (x : R) :
  irrational_unit_interval x -> exists a t,
    irrational_unit_interval t /\ x = continued_fraction_branch a t.
Proof.
move=> [hx [hx1 hirr]].
have hi : 1 < x^-1 by rewrite invf_gt1.
have /andP[hz0 hz1] := mem_rg1_floor (x^-1).
have hzpos : (0 : R) < (Num.floor (x^-1))%:~R.
  have hh := lt_trans hi hz1; by rewrite ltrDr in hh.
case he : (Num.floor (x^-1)) hz0 hz1 hzpos=> [n|n] hz0 hz1 hzpos.
- clear he; case: n hz0 hz1 hzpos=> [|a] hz0 hz1 hzpos; first by move: hzpos; rewrite /= ltxx.
  pose t : R := x^-1 - a.+1%:R.
  have ht0 : 0 <= t by rewrite /t subr_ge0.
  have ht1 : t < 1 by rewrite /t ltrBlDr addrC.
  have hxt : x = continued_fraction_branch a t.
    by rewrite /continued_fraction_branch /t addrC subrK invrK.
  have ht : 0 < t.
    rewrite lt_neqAle ht0 andbT; apply/eqP=> he0.
    apply: hirr; rewrite hxt -he0.
    exact: continued_fraction_zero_tail_rational.
  exists a,t; split=> //; split=> //; split=> // hr.
  apply: hirr; rewrite hxt; exact: continued_fraction_branch_rational ht hr.
- by move: hzpos; rewrite /= ltrNr oppr0 ltrn0.
Qed.

(** Source for [irrational_continued_fraction_four_steps]:
    supporting four-digit cylinder coverage for the continued
    fraction in Federer 2.2.9, p. 65. Iterating
    the proved irrational remainder step four times gives one
    block and another irrational interior tail. *)
Lemma irrational_continued_fraction_four_steps (R : realType) (x : R) :
  irrational_unit_interval x -> exists d t,
    irrational_unit_interval t /\ x = continued_fraction_block d t.
Proof.
move=> hx; have [a [x1 [h1 e1]]] := irrational_continued_fraction_step hx.
have [b [x2 [h2 e2]]] := irrational_continued_fraction_step h1.
have [c [x3 [h3 e3]]] := irrational_continued_fraction_step h2.
have [d [t [ht e4]]] := irrational_continued_fraction_step h3.
exists ((a,b),(c,d)),t; split=> //.
by rewrite /continued_fraction_block /= -e4 -e3 -e2 -e1.
Qed.
