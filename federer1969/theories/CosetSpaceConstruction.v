(** Federer (1969), 2.7.1, printed p. 122: existence of the space G/S of
    left cosets of a subgroup S of a group G, with the quotient topology, as
    specified by is_left_coset_space in CosetSpaceUP.v. The witness is the
    MathComp quotient of G by the equivalence relation g S = h S, which is
    an equivalence relation for every subset S, equipped with the MathComp
    quotient topology (quotient_topology.v). It is a construction module:
    only CosetSpaceSealed.v and tests/Assumptions.v may import it. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws CosetSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope quotient_scope.

Section CosetSpaceConstruction.
Variables (G : topologicalType) (mul : G -> G -> G) (S : set G).

(** Source for [coset_relation]: the relation g S = h S between
    elements of G, whose classes are the points of G/S in Federer
    2.7.1, p. 122. Construction. *)
Definition coset_relation : rel G := fun g h => `[< left_coset mul g S = left_coset mul h S >].

(** Source for [coset_relation_refl]: reflexivity of the coset
    relation, supporting the construction of G/S for Federer 2.7.1,
    p. 122. *)
Lemma coset_relation_refl : reflexive coset_relation.
Proof. by move=> g; apply/asboolP. Qed.

(** Source for [coset_relation_sym]: symmetry of the coset relation,
    supporting the construction of G/S for Federer 2.7.1, p. 122. *)
Lemma coset_relation_sym : symmetric coset_relation.
Proof. by move=> g h; apply/idP/idP=> /asboolP hgh; apply/asboolP. Qed.

(** Source for [coset_relation_trans]: transitivity of the coset
    relation, supporting the construction of G/S for Federer 2.7.1,
    p. 122. *)
Lemma coset_relation_trans : transitive coset_relation.
Proof. by move=> h g k /asboolP hgh /asboolP hhk; apply/asboolP; rewrite hgh. Qed.

(** Source for [coset_equivalence]: the coset relation as a MathComp
    equivalence relation, supporting the construction of G/S for
    Federer 2.7.1, p. 122. Construction. *)
Definition coset_equivalence : equiv_rel G :=
  EquivRel coset_relation coset_relation_refl coset_relation_sym coset_relation_trans.

(** Source for [coset_space_witness]: the quotient of G by the coset
    relation with the quotient topology, a witness for the space G/S of
    Federer 2.7.1, p. 122. Construction. *)
Definition coset_space_witness : topologicalType := quotient_topology {eq_quot coset_equivalence}.

(** Source for [coset_projection_witness]: the quotient map
    g |-> g S of the witness, Federer 2.7.1, p. 122. Construction. *)
Definition coset_projection_witness : G -> coset_space_witness :=
  \pi_(quotient_topology {eq_quot coset_equivalence}).

(** Source for [coset_projection_witness_eq]: two elements have the
    same image in the witness if and only if their cosets agree,
    supporting the construction of G/S for Federer 2.7.1, p. 122. *)
Lemma coset_projection_witness_eq g h :
  coset_projection_witness g = coset_projection_witness h <-> left_coset mul g S = left_coset mul h S.
Proof.
have hpi : forall k, coset_projection_witness k = \pi_({eq_quot coset_equivalence}) k by [].
rewrite !hpi; split.
- by move/eqmodP=> /asboolP.
- by move=> hgh; apply/eqmodP; apply/asboolP.
Qed.

(** Source for [coset_space_witness_laws]: the witness satisfies the
    specification of G/S for a subgroup S of a group G, Federer 2.7.1,
    p. 122. Existence proof. *)
Theorem coset_space_witness_laws (inv : G -> G) (e : G) :
  is_group_laws mul inv e -> is_subgroup mul inv e S ->
  is_left_coset_space mul inv S coset_projection_witness.
Proof.
move=> hG hS; constructor.
- by move=> q; exists (repr q); exact: reprK.
- move=> g h; have hc := left_coset_eq hG g h hS.
  have hw := coset_projection_witness_eq g h.
  by split=> hgh; [apply/hc/hw|apply/hw/hc].
- by move=> U.
Qed.

End CosetSpaceConstruction.
