(** Federer (1969), 3.3.20, p. 307: unions of actual square images. *)
From mathcomp Require Import all_boot finmap boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cell_union_image]: supporting exact image of
    the original finite square union under the local similarity of
    3.3.20, p. 307. Only the original cell-image laws are used;
    empty families and noninjective maps remain allowed. *)
Lemma finite_cell_union_image (I J X Y:choiceType) (F:{fset I})
    (f:I->J) (g:X->Y) (S:I->set X) (V:J->set Y):
  (forall i,i \in F ->V (f i)=g @` S i) ->
  (\bigcup_(j in [set` [fset f i|i in F]]) V j)=
    g @` (\bigcup_(i in [set` F]) S i).
Proof.
move=>hCells;apply/seteqP;split=>y.
- move=>[j /imfsetP[i hi ->] hy].
  rewrite hCells // in hy;have [x hx hValue]:=hy.
  exists x=>//;exists i;[exact:hi|exact:hx].
- move=>[x [i hi hx] hValue].
  exists (f i);first by apply/imfsetP;exists i.
  rewrite hCells //;by exists x.
Qed.
