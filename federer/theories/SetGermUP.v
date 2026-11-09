(** Federer (1969), 3.4.5, pp. 319–320: set germs
    and their induced Boolean operations, specified by original sets. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import LocalGermUP LocalGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_space]: the set germs of X at a,
    3.4.5, pp. 319–320. The opaque carrier uses local
    equality of membership propositions. *)
Definition set_germ_space (X:topologicalType) (a:X):choiceType:=
  @LocalGerms.space X Prop [the choiceType of set X] (fun S=>S) a.

(** Source for [set_germ]: the original notation for the germ
    of a set S at a, 3.4.5, p. 319. *)
Definition set_germ (X:topologicalType) (a:X) (S:set X):set_germ_space a:=
  @LocalGerms.germ X Prop [the choiceType of set X] (fun S=>S) a S.

(** Source for [is_set_germ_operations]: the induced union,
    intersection and complement operations in 3.4.5, pp. 319–320,
    specified by their equations on every original representative. *)
Record is_set_germ_operations (X:topologicalType) (a:X)
    (join meet:set_germ_space a->set_germ_space a->set_germ_space a)
    (neg:set_germ_space a->set_germ_space a):Prop:={
  (** Source for [set_germ_union_equation]: union of germs is
      induced by union of sets, 3.4.5, pp. 319–320. *)
  set_germ_union_equation:forall S T,join (set_germ a S) (set_germ a T)=set_germ a (S `|` T);
  (** Source for [set_germ_intersection_equation]: intersection of
      germs is induced by set intersection, 3.4.5, pp. 319–320. *)
  set_germ_intersection_equation:forall S T,meet (set_germ a S) (set_germ a T)=set_germ a (S `&` T);
  (** Source for [set_germ_complement_equation]: complement of a
      germ is induced by set complement, 3.4.5, pp. 319–320. *)
  set_germ_complement_equation:forall S,neg (set_germ a S)=set_germ a (~` S)
}.
