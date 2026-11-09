(** Federer (1969), 3.3.20, p. 308:
    a point in an original cell has positive finite-stage hit mass. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal.
From Federer Require Import FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cell_hit_point_positive]: supporting
    zero-diameter qualification of the auxiliary proposition
    in 3.3.20, p. 308. A point lying
    in one actual cell has at least one hit;
    every strictly positive weight gives positive mass. *)
Lemma finite_cell_hit_point_positive (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu:set X->\bar R) (x:X):
  is_finite_cell_hit_measure F S w mu ->0<w ->
  (exists i,i \in F /\S i x) ->(0<mu [set x])%E.
Proof.
move=>hMu hw [i [hi hx]].
have hHit:i \in finite_cell_hit_indices F S [set x].
  apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
have hSubset:([fset i] `<=` finite_cell_hit_indices F S [set x])%fset.
  apply/fsubsetP=>k;rewrite in_fset1=>/eqP->;exact:hHit.
have hCount:=fsubset_leq_card hSubset.
rewrite cardfs1 in hCount.
have hCountPositive:0<(#|` finite_cell_hit_indices F S [set x]|%:R:R) by rewrite ltr0n.
rewrite hMu lte_fin;exact:mulr_gt0 hCountPositive hw.
Qed.
