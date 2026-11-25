(** Federer (1969), 3.3.19, p. 304: a
    test set may be intersected with a carrier containing
    all actual fine cells without changing its original
    finite hit measure. This is an exact all-set identity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal.
From Federer Require Import FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cell_hit_support_restriction]: the
    actual finer psi sees only the original coarse
    level union, supporting the finite cyclic sum
    in 3.3.19, p. 304. No measurability
    of the original test set is assumed. *)
Lemma finite_cell_hit_support_restriction (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu:set X->\bar R) (P T:set X):
  is_finite_cell_hit_measure F S w mu ->
  (forall i,i \in F ->S i `<=` P) ->mu T=mu (T `&` P).
Proof.
move=>hMu hSupport.
have hIndices:finite_cell_hit_indices F S T=finite_cell_hit_indices F S (T `&` P).
  apply/fsetP=>i;apply/idP/idP.
  - move=>/finite_cell_hit_indices_membership[hi [x [hxS hxT]]].
    apply/finite_cell_hit_indices_membership;split=>//;exists x;split=>//.
    split=>//;exact:hSupport i hi x hxS.
  - move=>/finite_cell_hit_indices_membership[hi [x [hxS [hxT _]]]].
    apply/finite_cell_hit_indices_membership;split=>//;exists x;by split.
by rewrite !hMu hIndices.
Qed.
