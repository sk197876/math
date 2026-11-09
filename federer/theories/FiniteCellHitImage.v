(** Federer (1969), 3.3.20, pp. 307–308: original hit counts under a similarity. *)
From mathcomp Require Import all_boot all_order finmap boolp classical_sets.
From Federer Require Import FiniteCellHitMeasureUP FiniteCellHitIndicesLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cell_hit_image_indices]: supporting exact
    count transfer in the original similarity reduction of 3.3.20,
    pp. 307–308. Exact cell images give the image of the actual hit
    family under an injective map; the test set remains arbitrary. *)
Lemma finite_cell_hit_image_indices (I J X Y:choiceType)
    (F:{fset I}) (f:I->J) (g:X->Y) (S:I->set X) (V:J->set Y) (T:set Y):
  injective f ->(forall i,i \in F ->V (f i)=g @` S i) ->
  finite_cell_hit_indices [fset f i|i in F] V T=
    [fset f i|i in finite_cell_hit_indices F S (g @^-1` T)].
Proof.
move=>hF hCells;apply/fsetP=>j;apply/idP/idP.
- move=>/finite_cell_hit_indices_membership[/imfsetP[i hi ->] [y [hy hyT]]].
  rewrite hCells // in hy;have [x hx hxy]:=hy.
  apply/imfsetP;exists i=>//;apply/finite_cell_hit_indices_membership;split=>//.
  exists x;split=>//;by rewrite /= hxy.
- move=>/imfsetP[i /finite_cell_hit_indices_membership[hi [x [hx hxT]]] ->].
  apply/finite_cell_hit_indices_membership;split.
  + apply/imfsetP;by exists i.
  + exists (g x);split=>//;rewrite hCells //;by exists x.
Qed.

(** Source for [finite_cell_hit_image_cardinality]: the literal
    original number of hits is invariant under the cell identification
    in 3.3.20, pp. 307–308; no measure-scaling law is assumed. *)
Lemma finite_cell_hit_image_cardinality (I J X Y:choiceType)
    (F:{fset I}) (f:I->J) (g:X->Y) (S:I->set X) (V:J->set Y) (T:set Y):
  injective f ->(forall i,i \in F ->V (f i)=g @` S i) ->
  #|` finite_cell_hit_indices [fset f i|i in F] V T|=
    #|` finite_cell_hit_indices F S (g @^-1` T)|.
Proof.
move=>hF hCells;rewrite (@finite_cell_hit_image_indices I J X Y F f g S V T hF hCells).
exact:card_imfset.
Qed.
