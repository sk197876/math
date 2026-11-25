(** Federer (1969), proof of 2.4.4(2), p. 83: consequences of the abstract
    geometric-cell specification. No choice witness is unfolded. Source
    editions: GeometricQuantisationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint reals.
From Federer Require Import GeometricQuantisationUP GeometricIntegerCells.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [geometric_quantisation_bounds]: the inequalities
    u<=f<=t*u underlying the proof of Federer 2.4.4(2),
    p. 83, for nonnegative finite values. *)
Lemma geometric_quantisation_bounds (R : realType) (t : R) (q : R -> R) :
  1 < t -> is_geometric_quantisation t q -> forall x,
  0 <= x -> 0 <= q x /\ q x <= x /\ x <= t*q x.
Proof.
move=> ht hq x hx; have ht0 : 0 < t := lt_trans ltr01 ht.
have [hx0|hx0] := eqVneq x 0.
- rewrite hx0 (hq.1 0 (lexx 0)) mulr0; by split=> //; split.
- have hp : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
  have [j [hl [hu he]]] := hq.2 x hp.
  rewrite he; split; first exact: ltW (exprz_gt0 _ ht0).
  split=> //; apply: ltW.
  by move: hu; rewrite expfzDr ?gt_eqF // expr1z mulrC.
Qed.

(** Source for [geometric_quantisation_cell_value]: the
    approximant has the lower endpoint value on each of the
    cells in Federer 2.4.4(2), p. 83. *)
Lemma geometric_quantisation_cell_value (R : realType) (t : R) (q : R -> R) :
  1 < t -> is_geometric_quantisation t q -> forall x (j : int),
  t^j <= x -> x < t^(j+1) -> q x=t^j.
Proof.
move=> ht hq x j hl hu; have ht0 : 0 < t := lt_trans ltr01 ht.
have hx : 0 < x := lt_le_trans (exprz_gt0 j ht0) hl.
have [i [hil [hiu hi]]] := hq.2 x hx.
have he := geometric_integer_cell_unique ht hil hiu hl hu.
by rewrite hi he.
Qed.

(** Source for [geometric_quantisation_positive_fibre]: the
    exact level-set description for the geometric approximant in
    Federer 2.4.4(2), p. 83; this supports its measurability. *)
Lemma geometric_quantisation_positive_fibre (R : realType) (t : R) (q : R -> R) :
  1 < t -> is_geometric_quantisation t q -> forall x (j : int),
  q x=t^j <-> t^j <= x /\ x < t^(j+1).
Proof.
move=> ht hq x j; have ht0 : 0 < t := lt_trans ltr01 ht.
split; last by move=> [hl hu]; exact (@geometric_quantisation_cell_value R t q ht hq x j hl hu).
move=> he; have [hx|hx] := leP x 0.
- have hz := hq.1 x hx.
  have hh := exprz_gt0 j ht0; by rewrite -he hz ltxx in hh.
- have [i [hl [hu hi]]] := hq.2 x hx.
  have hij : i=j.
    have ht1 : t != 1 by rewrite gt_eqF.
    apply: (@ieexprIz R t ht0 ht1); by rewrite -hi -he.
  by rewrite -hij; split.
Qed.

(** Source for [geometric_quantisation_zero_fibre]: the
    zero level is exactly the nonpositive half-line for the
    approximant in Federer 2.4.4(2), p. 83. *)
Lemma geometric_quantisation_zero_fibre (R : realType) (t : R) (q : R -> R) :
  1 < t -> is_geometric_quantisation t q -> forall x, q x=0 <-> x<=0.
Proof.
move=> ht hq x; split; last exact: hq.1 x.
move=> hz; rewrite leNgt; apply/negP=> hx.
have [j [hl [hu he]]] := hq.2 x hx.
have hh := exprz_gt0 j (lt_trans ltr01 ht).
by rewrite -he hz ltxx in hh.
Qed.
