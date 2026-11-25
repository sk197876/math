(** General topology supporting Federer (1969), 3.4.9,
    p. 337: count the actual components meeting a
    neighbourhood, whether indexed by their original points
    or by the component subsets themselves. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [component_image_locally_finite]: the locally
    finite family of all components in 3.4.9,
    p. 337. Components meeting an open set
    are precisely the components based at points of
    the original set in that open set. *)
Theorem component_image_locally_finite (X:topologicalType) (U A:set X):
  (forall a,U a ->exists O:set X,open O /\O a /\
    finite_set (connected_component A @` (A `&` O))) ->
  @is_locally_finite_family_on X [the choiceType of (set X)] U
    (connected_component A @` A) (fun C=>C).
Proof.
move=>hLocal a ha;have [O [hO [hOa hFinite]]]:=hLocal a ha.
exists O;split;first exact:hO.
split;first exact:hOa.
apply:(sub_finite_set _ hFinite)=>C [[x hx hC] [y [hyO hyC]]].
have hy:connected_component A x y by rewrite hC.
have hyA:=@connected_component_sub X A x y hy.
exists y;first by split.
rewrite -hC;exact:esym (@same_connected_component X A x y hy).
Qed.
