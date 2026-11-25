(** Federer (1969), 3.4.5, p. 321: finite
    unions of original set germs. The finite fold is
    derived solely from the opaque Boolean operations; it
    chooses no set representative or new geometric object. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_finite_union]: the finite union
    of components in 3.4.5, p. 321, expressed
    through the public union and empty-germ operations. *)
Definition set_germ_finite_union (X:topologicalType) (a:X) (F:seq (set_germ_space a)):=
  foldr (@SetGerms.join X a) (@set_germ X a set0) F.

Section FiniteUnion.
Variable X:topologicalType.
Variable a:X.
Local Notation G:=(set_germ_space a).
Local Notation join:=(@SetGerms.join X a).
Local Notation union:=(@set_germ_finite_union X a).

(** Source for [set_germ_finite_union_cat]: concatenating
    finite component lists takes the union of their
    original finite unions, 3.4.5, p. 321. *)
Lemma set_germ_finite_union_cat (F H:seq G):union (F++H)=join (union F) (union H).
Proof.
elim:F=>[|alpha F ih] /=.
- rewrite set_germ_union_commutative;exact:esym (set_germ_union_empty (union H)).
- by rewrite ih set_germ_union_associative.
Qed.

(** Source for [set_germ_finite_union_member]: each original
    finite-family member is contained in its union,
    3.4.5, p. 321. *)
Lemma set_germ_finite_union_member (F:seq G) (alpha:G):alpha \in F ->set_germ_subset alpha (union F).
Proof.
elim:F=>[|beta F ih];first by rewrite in_nil.
rewrite in_cons=>/orP [/eqP ->|hAlpha] /=.
- exact:set_germ_subset_join_left.
- exact:(set_germ_subset_transitive (ih hAlpha) (set_germ_subset_join_right beta (union F))).
Qed.

(** Source for [set_germ_finite_union_bound]: a common
    upper germ contains the actual finite union,
    3.4.5, p. 321. *)
Lemma set_germ_finite_union_bound (F:seq G) (alpha:G):
  (forall beta,beta \in F ->set_germ_subset beta alpha) ->set_germ_subset (union F) alpha.
Proof.
elim:F=>[|beta F ih] hBound;first exact:set_germ_empty_subset.
apply:set_germ_subset_join_bound.
- exact:hBound beta (mem_head beta F).
- apply:ih=>gamma hGamma;apply:hBound;by rewrite in_cons hGamma orbT.
Qed.
End FiniteUnion.
