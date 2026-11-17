(** Federer (1969), 3.4.10, p. 337:
    finite local assembly of finite Hausdorff masses.
    This supporting connection applies the existing binary
    outer-measure bound; it imposes no measurability condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_binary_union_finite_mass]: finite
    subadditivity in the compact local assembly of
    3.4.10, p. 337, for arbitrary original
    sets and the existing outer-measure interface. *)
Theorem measure_binary_union_finite_mass (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A B:set X):
  is_measure mu ->mu A< +oo ->mu B< +oo ->mu (A `|` B)< +oo.
Proof.
move=>hMu hA hB.
have hValue S (hS:mu S< +oo):mu S=(fine (mu S))%:E.
  have hFinite:mu S \is a fin_num.
    rewrite ge0_fin_numE;first exact:hS.
    exact:measure_nonnegative hMu S.
  by rewrite fineK.
apply:(le_lt_trans (measure_binary_cover hMu (fun x hx=>hx))).
by rewrite (hValue A hA) (hValue B hB) -EFinD ltry.
Qed.
