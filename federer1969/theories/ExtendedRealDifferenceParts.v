(** Federer (1969), 2.1.1(4)-(7), pp. 52-53: positive and negative parts of
    a difference. Source context: ExtendedRealPartial.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_difference_positive_bound]: Federer
    2.1.1(7), p. 53; supporting bound of the positive variation
    of u-v by u when both summands are nonnegative. *)
Lemma nonnegative_difference_positive_bound (R : realType) (u v : \bar R) :
  0 <= u -> 0 <= v -> extended_positive_part (u-v) <= u.
Proof.
move=> hu hv; rewrite /extended_positive_part ge_max hu andbT.
have hb : u-v <= u by rewrite -[leRHS]adde0; apply: leeD2l; by rewrite oppe_le0.
by rewrite hb.
Qed.

(** Source for [nonnegative_difference_negative_bound]: Federer
    2.1.1(7), p. 53; supporting bound of the negative variation
    of a defined u-v by v. The difference must be defined. *)
Lemma nonnegative_difference_negative_bound (R : realType) (u v : \bar R) :
  0 <= u -> 0 <= v -> adde_def u (-v) ->
  extended_negative_part (u-v) <= v.
Proof.
move=> hu hv hd; rewrite /extended_negative_part oppeB // addeC.
exact: nonnegative_difference_positive_bound.
Qed.

(** Source for [nonnegative_difference_parts_balance]: Federer
    2.1.1(7), p. 53; supporting balanced identity for the parts
    of a defined difference, prior to summation. *)
Lemma nonnegative_difference_parts_balance (R : realType) (u v : \bar R) :
  0 <= u -> 0 <= v -> adde_def u (-v) ->
  extended_positive_part (u-v) + v = extended_negative_part (u-v) + u.
Proof.
case: u=> [u| |]; case: v=> [v| |] //= hu hv hd;
  rewrite /extended_negative_part /extended_positive_part //=.
- have [hle|hlt] := leP v u.
  + have hp : 0 <= (u-v)%:E by rewrite lee_fin subr_ge0.
    have hn : (- (u-v))%:E <= 0 by rewrite lee_fin oppr_le0 subr_ge0.
    rewrite (max_l hp) (max_r hn).
    by rewrite add0e -EFinD subrK.
  + have hn : (u-v)%:E <= 0 by rewrite lee_fin subr_le0; exact: ltW hlt.
    have hp : 0 <= (- (u-v))%:E by rewrite lee_fin oppr_ge0 subr_le0; exact: ltW hlt.
    rewrite (max_r hn) (max_l hp) add0e -EFinD opprB subrK.
    by [].
- by rewrite addeNy maxNye maxye add0e addye.
- have hvN : (-v)%:E != (-oo : \bar R) by [].
  by rewrite (@addye R (-v)%:E hvN) maxye maxNye add0e addye.
Qed.
