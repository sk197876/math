(** Federer (1969), 2.6.4, pp. 118–119: supporting estimate for a nearly
    optimal measurable cover in the density proof. This is the splitting
    identity in 2.1.2, p. 54, with finite-measure cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cover_measure_excess]: supporting excess
    bound in the characteristic approximation of Federer 2.6.4,
    pp. 118–119. Only the covered set is assumed measurable;
    the cover itself need not be measurable for this identity. *)
Lemma finite_cover_measure_excess (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S T : set X) (e : R) :
  measure_measurable mu S -> mu S < +oo -> S `<=` T ->
  mu T < mu S+e%:E -> mu (T `\` S) < e%:E.
Proof.
move=> hS hfin hST hT.
have hsfin : mu S \is a fin_num by rewrite ge0_fin_numE //; exact (@measure_nonnegative R X mu hm S).
have hi : T `&` S=S.
  apply/seteqP; split=> [x [_ hx]|x hx]=> //; split=> //; exact: hST hx.
by rewrite (hS T) hi lteD2lE // in hT.
Qed.
