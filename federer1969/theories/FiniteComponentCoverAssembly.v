(** Federer (1969), 3.4.8(11), pp. 333–335:
    finitely many sets with finitely many
    connected components form a finite connected
    cover of their union. This supporting
    lemma makes the component-counting step explicit. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import FiniteConnectedCoverComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_component_cover_assembly]:
    the finite union step in the
    dimension induction of 3.4.8(11),
    pp. 333–335. No relative openness
    or pairwise disjointness is required. *)
Theorem finite_component_cover_assembly (X:topologicalType) (I:Type)
    (D:set I) (S:I->set X) (A:set X):
  finite_set D ->
  (forall i,D i ->finite_set (connected_component (S i) @` S i)) ->
  (forall i,D i ->S i `<=` A) ->
  (forall x,A x ->exists i,D i /\ S i x) ->
  finite_set (connected_component A @` A).
Proof.
move=>hD hFinite hSub hCover.
pose F:=\bigcup_(i in D) (connected_component (S i) @` S i).
apply:(@finite_connected_cover_components X A F).
- exact:bigcup_finite hD hFinite.
- move=>C [i hi [x hx <-]];split.
  + move=>z hz;exact:hSub i hi z (@connected_component_sub X (S i) x z hz).
  + exact:component_connected.
- move=>x hx;have [i [hi hSix]]:=hCover x hx.
  exists (connected_component (S i) x);split.
  + exists i;first exact:hi.
    by exists x.
  + exact:connected_component_refl hSix.
Qed.
