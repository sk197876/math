(** Federer (1969), 2.4.16, p. 90: choose the first coefficient close enough
    to one that its contribution exceeds a prescribed smaller bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [concentrated_positive_coefficient]: supporting
    choice of the first weight near one in Federer 2.4.16,
    p. 90, after the second integral display. *)
Lemma concentrated_positive_coefficient (R : realType) (r t : R) :
  0 <= r -> r < t -> exists d, 0 < d /\ d < 1 /\ r < (1-d)*t.
Proof.
move=> hr hrt; have ht : 0 < t := le_lt_trans hr hrt.
have [hrm hmt] := midf_lt hrt.
pose c := ((r+t)/2) / t.
have hc0 : 0 < c by rewrite /c divr_gt0 //; exact: le_lt_trans hr hrm.
have hc1 : c < 1 by rewrite /c ltr_pdivrMr // mul1r.
exists (1-c); split; first by rewrite subr_gt0.
split; first by rewrite ltrBlDl ltrDr.
by rewrite opprB addrCA subrr addr0 /c mulfVK ?gt_eqF.
Qed.
