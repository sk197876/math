(** Federer (1969), 2.2.9, p. 65, supporting exclusion of rational points
    from infinite interior continued fractions. A positive rational
    remainder has a strictly smaller positive denominator after one Gauss
    step. This is the elementary Euclidean descent behind Bell2016, section
    1, p. 1, where rational expansions terminate. The proof uses
    integer-ratio arithmetic and natural well-foundedness, not an external
    continued-fraction termination theorem. Source context:
    ContinuedFractionBranches.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ContinuedFractionBranches ContinuedFractionBlocks RationalRealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_rational_tail]: supporting
    denominator descent for Federer 2.2.9, p. 65.
    If 1/(a+1+t)=p/q and 0<t<1, then t=r/p
    for a natural r strictly between zero and p. *)
Lemma continued_fraction_rational_tail (R : realType) a p q (t : R) :
  (0 < p)%N -> (0 < q)%N -> 0 < t -> t < 1 ->
  continued_fraction_branch a t = p%:R / q%:R ->
  exists r : nat, (0 < r)%N /\ (r < p)%N /\ t = r%:R / p%:R.
Proof.
move=> hp hq ht ht1 he.
have hpR : (0 : R) < p%:R by rewrite ltr0n.
have hp0 : (p%:R : R) != 0 by rewrite gt_eqF.
have hden : a.+1%:R + t = q%:R / p%:R.
  have hh := congr1 (fun x : R => x^-1) he.
  by rewrite continued_fraction_branch_reciprocal invf_div in hh.
have hqE : (q%:R : R) = (a.+1%:R + t) * p%:R by rewrite hden divfK.
have hrem : (q%:R : R) - a.+1%:R * p%:R = t * p%:R.
  by rewrite hqE mulrDl addrAC subrr add0r.
have hpos : (0 : R) < q%:R - a.+1%:R * p%:R.
  rewrite hrem; exact: mulr_gt0 ht hpR.
have hn : ((a.+1 * p)%N < q)%N.
  by move: hpos; rewrite subr_gt0 -natrM ltr_nat.
pose r := (q - a.+1 * p)%N.
have hrE : (r%:R : R) = q%:R - a.+1%:R * p%:R.
  by rewrite /r natrB ?(ltnW hn) // natrM.
have hr : (0 < r)%N by rewrite -(ltr0n R) hrE.
have htE : t = (r%:R : R)/p%:R by rewrite hrE hrem mulfK.
have hrp : (r < p)%N.
  by move: ht1; rewrite htE ltr_pdivrMr // mul1r ltr_nat.
by exists r; split=> //; split.
Qed.

(** Source for [continued_fraction_block_rational_descent]:
    supporting strict decrease of a positive rational denominator
    through a four-digit block for Federer 2.2.9, p. 65.
    Every intermediate tail lies strictly between zero and one. *)
Lemma continued_fraction_block_rational_descent (R : realType) d p q (t : R) :
  (0 < p)%N -> (p < q)%N -> 0 < t -> t < 1 ->
  continued_fraction_block d t = p%:R / q%:R ->
  exists r s : nat, (0 < r)%N /\ (r < s)%N /\ (s < q)%N /\ t = r%:R / s%:R.
Proof.
move=> hp hpq ht ht1; case: d=> [[a b] [c d]]; rewrite /continued_fraction_block /= => he.
have hq : (0 < q)%N := ltn_trans hp hpq.
have bounds n (x : R) (hx : 0 < x) :
    0 < continued_fraction_branch n x /\ continued_fraction_branch n x < 1.
  split; first exact: (continued_fraction_branch_unit_bounds n (ltW hx)).1.
  exact: continued_fraction_branch_positive_tail hx.
have [hd hd1] := bounds d t ht; have [hc hc1] := bounds c _ hd.
have [hb hb1] := bounds b _ hc.
have [p1 [hp1 [h1 e1]]] := @continued_fraction_rational_tail R a p q _ hp hq hb hb1 he.
have [p2 [hp2 [h2 e2]]] := @continued_fraction_rational_tail R b p1 p _ hp1 hp hc hc1 e1.
have [p3 [hp3 [h3 e3]]] := @continued_fraction_rational_tail R c p2 p1 _ hp2 hp1 hd hd1 e2.
have [r [hr [hr3 er]]] := @continued_fraction_rational_tail R d p3 p2 t hp3 hp2 ht ht1 e3.
exists r,p3; split=> //; split=> //; split=> //.
exact: ltn_trans h3 (ltn_trans h2 (ltn_trans h1 hpq)).
Qed.
