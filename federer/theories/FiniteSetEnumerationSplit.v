(** Federer (1969), 2.6.6, p. 120: split b into a and b-a in the
    finite-marginal consistency equation. This is supporting finite-set
    enumeration infrastructure, not a separate book claim. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [finite_set_enumeration_split]: enumeration of b is
    a permutation of an enumeration of a followed by one of b-a,
    for the consistency calculation in Federer 2.6.6, p. 120. *)
Lemma finite_set_enumeration_split (I : choiceType) (F G : {fset I}) :
  {subset F <= G} -> perm_eq (enum_fset G) (enum_fset F ++ enum_fset (G `\` F)).
Proof.
move=> hFG; apply: uniq_perm; first exact: fset_uniq.
- rewrite cat_uniq !fset_uniq andbT /=; apply/hasPn=> i hi.
  by move: hi; rewrite in_fsetD=> /andP[].
- move=> i; rewrite mem_cat in_fsetD.
  case: (boolP (i \in F))=> hi; first by rewrite hFG.
  by rewrite /=.
Qed.
