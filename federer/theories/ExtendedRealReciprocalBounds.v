(** Federer (1969), 2.1.5, p. 57, supporting approximation for the
    measurable-superset infimum. Only the existing complete Archimedean
    real-field background is used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_reciprocal_nat_small]: Federer
    2.1.5, p. 57, supporting Archimedean step for an approximating
    sequence of measurable supersets; not a separately stated book claim. *)
Lemma positive_reciprocal_nat_small (R : realType) (d : R) :
  (0 < d)%R -> exists n, (((n.+1)%:R : R)^-1 < d)%R.
Proof.
move=> hd; pose n := Num.bound d^-1.
have hb : (d^-1 < n%:R)%R by apply: archi_boundP; rewrite invr_ge0; exact: ltW hd.
exists n; rewrite invf_plt ?inE ?ltr0n //.
- apply: lt_le_trans hb _; by rewrite ler_nat.
- change (0 < (n.+1%:R : R))%R; by rewrite ltr0n.
Qed.

(** Source for [extended_real_reciprocal_upper_bound]: Federer
    2.1.5, p. 57, supporting limit of the infimum approximation:
    an extended real below r+1/(n+1) for every n is at most r. *)
Lemma extended_real_reciprocal_upper_bound (R : realType) (x : \bar R) (r : R) :
  (forall n, x <= (r + ((n.+1)%:R)^-1)%:E) -> x <= r%:E.
Proof.
case: x=> [s| |] h; last exact: leNye.
- rewrite lee_fin leNgt; apply/negP=> hrs.
  have hd : (0 < s-r)%R by rewrite subr_gt0.
  have [n hn] := positive_reciprocal_nat_small hd.
  have hl : (r + ((n.+1)%:R)^-1 < r + (s-r))%R by rewrite ltrD2l.
  rewrite [(r + (s-r))%R]addrC subrK in hl.
  have hb := h n; rewrite lee_fin in hb.
  by have := lt_le_trans hl hb; rewrite ltxx.
- have hb := h 0%N; by rewrite leNgt ltry in hb.
Qed.
