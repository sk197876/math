(** Federer (1969), 3.3.20, p. 308:
    the exact original missing-cell count complements the hit count. *)
From mathcomp Require Import all_boot all_order finmap boolp classical_sets.
From Federer Require Import FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_cell_missing_count_identity]: the
    defining count r_j in 3.3.20, p. 308.
    Actual hit and missed subfamilies partition the
    original finite cells, including an empty test set. *)
Lemma finite_cell_missing_count_identity (I X:choiceType)
    (F:{fset I}) (S:I->set X) (T:set X):
  (#|` (F `\` finite_cell_hit_indices F S T)|+#|` finite_cell_hit_indices F S T|)%N=#|` F|.
Proof.
have hSub:=@finite_cell_hit_indices_subset I X F S T.
have hCard:=fsubset_leq_card hSub.
by rewrite cardfsDS // subnK.
Qed.
