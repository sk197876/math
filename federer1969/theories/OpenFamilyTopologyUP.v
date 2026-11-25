(** Federer (1969), 4.1.1, pp. 343–345: the smooth-function topology,
    its fixed-support subspaces and the final test-function topology.
    These general-topology laws are supporting infrastructure. They keep
    a topology independent of any construction or vector-space structure. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_open_family_topology]: supporting open-set laws for
    the topologies in Federer 4.1.1, pp. 343–345. In words: the whole
    space, finite intersections and arbitrary unions are open. *)
Record is_open_family_topology (X : Type) (O : set (set X)) : Prop := {
  (** Source for [open_family_whole]: the whole-space law supporting
      the topology of E(U,Y), Federer 4.1.1, p. 344. *)
  open_family_whole : O setT;
  (** Source for [open_family_intersection]: the finite-intersection law
      supporting Federer 4.1.1, p. 344. *)
  open_family_intersection : forall A B, O A -> O B -> O (A `&` B);
  (** Source for [open_family_union]: the arbitrary-union law supporting
      the open-set characterization in Federer 4.1.1, p. 344. *)
  open_family_union : forall (I : Type) (A : I -> set X),
    (forall i, O (A i)) -> O (\bigcup_i A i)
}.

(** Source for [open_family_neighbourhood]: a set containing an open
    neighbourhood of x, supporting the basic neighbourhoods in Federer
    4.1.1, p. 344. *)
Definition open_family_neighbourhood (X : Type) (O : set (set X))
    (x : X) (A : set X) :=
  exists B, O B /\ B x /\ B `<=` A.

(** Source for [open_family_continuous]: continuity by inverse images
    of open sets, supporting all topology comparisons in Federer 4.1.1,
    pp. 344–345. No linearity or local convexity is implicit. *)
Definition open_family_continuous (X Y : Type)
    (OX : set (set X)) (OY : set (set Y)) (f : X -> Y) :=
  forall A, OY A -> OX [set x | A (f x)].

(** Source for [open_family_continuous_identity]: supporting identity
    map for the topology comparisons in Federer 4.1.1, p. 344. *)
Lemma open_family_continuous_identity (X : Type) (O : set (set X)) :
  open_family_continuous O O (fun x => x).
Proof. by move=> A hA. Qed.

(** Source for [open_family_continuous_compose]: supporting composition
    law for the inclusions and dual restrictions in Federer 4.1.1,
    pp. 344–345. *)
Lemma open_family_continuous_compose (X Y Z : Type)
    (OX : set (set X)) (OY : set (set Y)) (OZ : set (set Z))
    (f : X -> Y) (g : Y -> Z) :
  open_family_continuous OX OY f -> open_family_continuous OY OZ g ->
  open_family_continuous OX OZ (fun x => g (f x)).
Proof.
move=> hf hg A hA.
exact: (hf [set y | A (g y)] (hg A hA)).
Qed.

(** Source for [open_family_neighbourhood_contains]: supporting centre
    membership of the basic neighbourhoods in Federer 4.1.1, p. 344. *)
Lemma open_family_neighbourhood_contains (X : Type) (O : set (set X)) x A :
  open_family_neighbourhood O x A -> A x.
Proof. by move=> [B [hB [hx hBA]]]; exact: hBA. Qed.

(** Source for [open_family_neighbourhood_enlarge]: supporting upward
    closure of neighbourhoods in Federer 4.1.1, p. 344. *)
Lemma open_family_neighbourhood_enlarge (X : Type) (O : set (set X)) x A B :
  A `<=` B -> open_family_neighbourhood O x A ->
  open_family_neighbourhood O x B.
Proof. by move=> hAB [C [hC [hx hCA]]]; exists C; split=> //; split=> // y hy; apply: hAB; exact: hCA. Qed.
