(** Opaque operations of the linear group of V, Federer (1969), 2.7.16,
    printed p. 134: "the automorphisms form a dense open subset of Hom(V,
    V), called the linear group of V". The signature exposes only the
    multiplication, the inversion and the identity of the type of members of
    the linear group and their specification is_linear_group_structure of
    LinearGroupTopology.v; downstream results use the specification, never
    the choice made here. The interface names linear_group_mul,
    linear_group_inv and linear_group_unit, the laws and the topological
    group theorem linear_group_operations_lch follow the module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP LinearBasis InnerMetric HomInner TopologicalGroupUP
  LinearGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type LinearGroupOperationsSignature.
  (** Source for [mul]: the multiplication (functional composition) of
      the linear group of V, Federer 2.7.16, p. 134, exposed through its
      specification. *)
  Parameter mul : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b),
    set_type (linear_group hB hb) -> set_type (linear_group hB hb) -> set_type (linear_group hB hb).
  (** Source for [inv]: the inversion of the linear group of V, Federer
      2.7.16, p. 134, exposed through its specification. *)
  Parameter inv : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b),
    set_type (linear_group hB hb) -> set_type (linear_group hB hb).
  (** Source for [unit]: the identity 1_V of the linear group of V,
      Federer 2.7.16, p. 134, exposed through its specification. *)
  Parameter unit : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b), set_type (linear_group hB hb).
  (** Source for [laws]: the specification of the operations of the
      linear group of V, Federer 2.7.16, p. 134. *)
  Parameter laws : forall (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b),
    is_linear_group_structure (@mul R V B hB n b hb) (@inv R V B hB n b hb) (@unit R V B hB n b hb).
End LinearGroupOperationsSignature.

Module LinearGroupOperations : LinearGroupOperationsSignature.
(** Source for [witness]: the operations of the linear group of V,
    Federer 2.7.16, p. 134, chosen from linear_group_structure_exists.
    Existence witness. *)
Definition witness (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :
  {t : (set_type (linear_group hB hb) -> set_type (linear_group hB hb) -> set_type (linear_group hB hb)) *
    (set_type (linear_group hB hb) -> set_type (linear_group hB hb)) * set_type (linear_group hB hb) |
    is_linear_group_structure t.1.1 t.1.2 t.2}.
Proof.
apply: cid.
have [mul [inv [e h]]] := linear_group_structure_exists hB hb.
by exists (mul, inv, e).
Defined.
(** Source for [mul]: witness of the multiplication of the linear group,
    Federer 2.7.16, p. 134. *)
Definition mul (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :=
  (sval (witness hB hb)).1.1.
(** Source for [inv]: witness of the inversion of the linear group,
    Federer 2.7.16, p. 134. *)
Definition inv (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :=
  (sval (witness hB hb)).1.2.
(** Source for [unit]: witness of the identity of the linear group,
    Federer 2.7.16, p. 134. *)
Definition unit (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :=
  (sval (witness hB hb)).2.
(** Source for [laws]: the chosen operations satisfy the specification
    of the linear group, Federer 2.7.16, p. 134. No new global
    assumption is introduced. *)
Lemma laws (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :
  is_linear_group_structure (@mul R V B hB n b hb) (@inv R V B hB n b hb) (@unit R V B hB n b hb).
Proof. exact: (svalP (witness hB hb)). Qed.
End LinearGroupOperations.

Section Interface.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation GL := (set_type (linear_group hB hb)).

(** Source for [linear_group_mul]: the multiplication g h = g o h of the
    linear group of V, Federer 2.7.16, p. 134. Interface name of the
    sealed operation. *)
Definition linear_group_mul : GL -> GL -> GL := @LinearGroupOperations.mul R V B hB n b hb.

(** Source for [linear_group_inv]: the inversion g |-> g^{-1} of the
    linear group of V, Federer 2.7.16, p. 134. Interface name of the
    sealed operation. *)
Definition linear_group_inv : GL -> GL := @LinearGroupOperations.inv R V B hB n b hb.

(** Source for [linear_group_unit]: the identity 1_V of the linear group
    of V, Federer 2.7.16, p. 134. Interface name of the sealed
    operation. *)
Definition linear_group_unit : GL := @LinearGroupOperations.unit R V B hB n b hb.

(** Source for [linear_group_operations]: the operations of the linear
    group of V are composition, inversion and 1_V, Federer 2.7.16,
    p. 134. Specification of the interface names. *)
Theorem linear_group_operations :
  is_linear_group_structure linear_group_mul linear_group_inv linear_group_unit.
Proof. exact: LinearGroupOperations.laws. Qed.

(** Source for [linear_group_operations_lch]: "the topological
    assumptions of our general theory are satisfied", Federer 2.7.16,
    p. 134: the linear group of V, with composition, inversion and 1_V
    and the relative topology of Hom(V, V), is a locally compact
    Hausdorff topological group in the sense of 2.7.1, p. 121. Direct
    formalisation. *)
Theorem linear_group_operations_lch :
  is_locally_compact_hausdorff_group linear_group_mul linear_group_inv linear_group_unit.
Proof. exact: linear_group_lch_group linear_group_operations. Qed.

End Interface.

Arguments linear_group_mul {R V B} hB {n b} hb.
Arguments linear_group_inv {R V B} hB {n b} hb.
Arguments linear_group_unit {R V B} hB {n b} hb.
