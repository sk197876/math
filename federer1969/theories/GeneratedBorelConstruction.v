(** Federer (1969), 2.2.1, pp. 59-60: existence of the smallest Borel family
    containing a family of subsets of X. This private witness intersects all
    containing Borel families; public consequences use the least-family
    specification instead. Source context: BorelFamilyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BorelFamilyUP BorelFamilyIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [generated_borel_family_exists]: Federer 2.2.1, pp. 59-60,
    existence by intersection The powerset of X is one containing Borel
    family, so the defining candidates are nonempty. *)
Lemma generated_borel_family_exists (I : choiceType) (X : set I)
    (S : set (set I)) :
  (forall A, S A -> A `<=` X) -> exists F, is_generated_borel_family X S F.
Proof.
move=> hS.
pose Omega := [set F | is_borel_family X F /\ S `<=` F].
pose F := [set A | A `<=` X /\ forall G, Omega G -> G A].
exists F; constructor.
- apply: borel_family_intersection=> G [hG _]; exact hG.
- move=> A hA; split; first exact: hS.
  move=> G [_ hs]; exact: hs.
- by move=> G hG hs A [_ ha]; apply: ha; split.
Qed.
