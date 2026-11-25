(** Federer (1969), 4.1.1, pp. 343–344: the derivative seminorms
    nu^i_K are directed by increasing derivative order and compact set.
    These independent laws support their basic-neighbourhood topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_directed_seminorm_family]: supporting laws of the
    family nu^i_K in Federer 4.1.1, pp. 343–344. Every two seminorms
    admit a common dominating member. Neither separation nor a topology
    is assumed in this specification. *)
Record is_directed_seminorm_family (R : realType) (E : lmodType R)
    (I : Type) (p : I -> E -> R) : Prop := {
  (** Source for [directed_seminorm_nonempty]: the order-zero,
      empty-compact-set index exists, Federer 4.1.1, pp. 343–344. *)
  directed_seminorm_nonempty : exists i : I, True;
  (** Source for [directed_seminorm_laws]: each nu^i_K is a finite-valued
      seminorm, Federer 4.1.1, pp. 343–344. *)
  directed_seminorm_laws : forall i, is_real_seminorm (p i);
  (** Source for [directed_seminorm_upper_pair]: union of compact sets
      and maximum derivative order dominate each pair, supporting the
      single-ball neighbourhood base in Federer 4.1.1, p. 344. *)
  directed_seminorm_upper_pair : forall i j, exists k,
    forall x, p i x <= p k x /\ p j x <= p k x
}.

(** Source for [is_seminorm_family_topology]: independent
    basic-neighbourhood specification for E(U,Y), Federer 4.1.1,
    p. 344. The topology is characterized by the printed translated
    seminorm balls; existence is proved separately. *)
Definition is_seminorm_family_topology (R : realType) (E : lmodType R)
    (I : Type) (p : I -> E -> R) (O : set (set E)) :=
  is_open_family_topology O /\ forall A,
    O A <-> forall x, A x -> exists i r, 0 < r /\
      forall y, p i (y-x) < r -> A y.

(** Source for [seminorm_family_separates]: supporting separation
    condition for the Hausdorff assertion about E(U,Y), Federer 4.1.1,
    p. 344. Applied there to order-zero values on singleton compacts. *)
Definition seminorm_family_separates (R : realType) (E : lmodType R)
    (I : Type) (p : I -> E -> R) :=
  forall x, (forall i, p i x = 0) -> x = 0.
