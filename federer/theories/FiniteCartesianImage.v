(** Federer (1969), 3.3.20, pp. 307–308: product families under original factor similarities. *)
From mathcomp Require Import all_boot finmap boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_cartesian_image]: supporting exact product-family
    image identity for the original square descendants in 3.3.20,
    pp. 307–308. Empty families and noninjective maps are allowed. *)
Lemma finite_cartesian_image (I J K L:choiceType) (A:{fset I}) (B:{fset J})
    (f:I->K) (g:J->L):
  ([fset f i|i in A] `*` [fset g j|j in B])%fset=
    [fset (f p.1,g p.2)|p in (A `*` B)%fset].
Proof.
apply/fsetP=>z;case:z=>x y;rewrite in_fsetM;apply/andP/imfsetP.
- move=>[/imfsetP[i hi hX] /imfsetP[j hj hY]].
  exists (i,j);first by rewrite in_fsetM hi hj.
  by rewrite /= -hX -hY.
- move=>[[i j] hp hEqual].
  move:hp;rewrite in_fsetM=>/andP[hi hj].
  have hX:x=f i:=congr1 fst hEqual.
  have hY:y=g j:=congr1 snd hEqual.
  split;apply/imfsetP;[by exists i|by exists j].
Qed.
