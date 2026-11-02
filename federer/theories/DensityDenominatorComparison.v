(** Denominator comparison supporting Federer (1969), 2.10.19(3)–(5), p.
    181. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import CaratheodoryDensityQuotient ExtendedRealConventions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [density_smaller_denominator_bound]: supporting ratio
    comparison in 2.10.19, p. 181 For nonnegative numerator, decreasing a
    positive radius denominator to a possibly zero cost increases the
    corrected quotient, including infinite numerator values. *)
Lemma density_smaller_denominator_bound (R : realType) (x c y : \bar R) (b : R) :
  0<=x -> 0<=c -> (0<b)%R -> c<=b%:E ->
  caratheodory_density_divide x c=Some y -> x/b%:E<=y.
Proof.
move=> hx hc hb hcb.
case: (eqVneq c 0)=> [->|hcn].
- case: (eqVneq x 0)=> [->|hxn].
  + rewrite caratheodory_density_divide_zero_zero=> -[<-]; by rewrite mul0e.
  + have hp : 0<x by rewrite lt_def hxn hx.
    rewrite (caratheodory_density_divide_positive_zero hp)=> -[<-]; exact: leey.
- have hcp : 0<c by rewrite lt_def hcn hc.
  have hcf : c < +oo := le_lt_trans hcb (@ltry R b).
  have hfin : c \is a fin_num by rewrite (ge0_fin_numE hc).
  rewrite (caratheodory_density_divide_nonzero x hcn) /extended_divide hcn hfin orbT=> -[<-].
  have hcmp : b%:E^-1<=c^-1.
    pose a := fine c.
    have he : c=a%:E by rewrite /a fineK.
    have ha : (0<a)%R by move: hcp; rewrite he lte_fin.
    have hab : (a<=b)%R by move: hcb; rewrite he lee_fin.
    by rewrite he !inver (gt_eqF hb) (gt_eqF ha) lee_fin lef_pV2.
  exact: (lee_wpmul2l hx hcmp).
Qed.
