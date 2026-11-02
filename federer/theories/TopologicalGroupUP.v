(** Federer (1969), 2.7.1, printed p. 121: "G a locally compact Hausdorff
    topological group". MathComp provides no structure of a noncommutative
    group on an infinite type, so a group is specified here by predicates on
    its multiplication, inversion and identity: the group laws, continuity
    of the multiplication on G x G and of the inversion. Local compactness
    and the Hausdorff property are the separate MathComp predicates
    locally_compact [set: G] and hausdorff_space G, as for the spaces of
    2.5.13; is_locally_compact_hausdorff_group combines the three
    conditions, the standing hypothesis on G in section 2.7. The group
    axioms are the one-sided ones (associativity, left identity, left
    inverses); the two-sided laws are derived in TopologicalGroupLaws.v.
    Subgroups and left cosets g S, used for the isotropy subgroups G^x and
    the space G/S of 2.7.1, p. 122, are specified in the same way. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_group_laws]: the group structure of the
    topological group G in Federer 2.7.1, p. 121, with identity e
    ("where e is the identity of G"). Definition by the one-sided group
    axioms; the right identity and right inverse laws follow. *)
Record is_group_laws (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G) : Prop := {
  (** Source for [group_mulA]: associativity of the group G of
      Federer 2.7.1, p. 121. *)
  group_mulA : forall g h k, mul g (mul h k) = mul (mul g h) k;
  (** Source for [group_mul1g]: e is a left identity of G, Federer
      2.7.1, p. 121. *)
  group_mul1g : forall g, mul e g = g;
  (** Source for [group_mulVg]: g^{-1} g = e, Federer 2.7.1, p. 121. *)
  group_mulVg : forall g, mul (inv g) g = e
}.

(** Source for [is_topological_group]: "G a ... topological group",
    Federer 2.7.1, p. 121. Definition: the group laws hold, the
    multiplication is continuous on the product space G x G, and the
    inversion is continuous. *)
Record is_topological_group (G : topologicalType) (mul : G -> G -> G) (inv : G -> G) (e : G) : Prop := {
  (** Source for [topological_group_laws]: the group laws of G,
      Federer 2.7.1, p. 121. *)
  topological_group_laws : is_group_laws mul inv e;
  (** Source for [topological_group_mul_continuous]: continuity of
      (g,h) |-> gh on G x G, Federer 2.7.1, p. 121. *)
  topological_group_mul_continuous : continuous (fun p : G * G => mul p.1 p.2);
  (** Source for [topological_group_inv_continuous]: continuity of
      g |-> g^{-1}, Federer 2.7.1, p. 121. *)
  topological_group_inv_continuous : continuous inv
}.

(** Source for [is_locally_compact_hausdorff_group]: "G a locally
    compact Hausdorff topological group", Federer 2.7.1, p. 121, the
    standing hypothesis on G in section 2.7. Definition combining
    is_topological_group with the MathComp predicates hausdorff_space
    and locally_compact, as for the spaces of 2.5.13. *)
Record is_locally_compact_hausdorff_group (G : topologicalType) (mul : G -> G -> G) (inv : G -> G)
    (e : G) : Prop := {
  (** Source for [lch_group_topological]: G is a topological group,
      Federer 2.7.1, p. 121. *)
  lch_group_topological : is_topological_group mul inv e;
  (** Source for [lch_group_hausdorff]: G is Hausdorff, Federer 2.7.1,
      p. 121. *)
  lch_group_hausdorff : hausdorff_space G;
  (** Source for [lch_group_locally_compact]: G is locally compact,
      Federer 2.7.1, p. 121. *)
  lch_group_locally_compact : locally_compact [set: G]
}.

(** Source for [is_subgroup]: the subgroups of Federer 2.7.1, p. 121,
    "the isotropy subgroup G^x", and p. 122, "Every closed subgroup S
    of G". Definition: S contains e and is closed under multiplication
    and inversion. *)
Record is_subgroup (G : Type) (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) : Prop := {
  (** Source for [subgroup_unit]: e belongs to the subgroup, Federer
      2.7.1, pp. 121–122. *)
  subgroup_unit : S e;
  (** Source for [subgroup_mul]: closure under multiplication, Federer
      2.7.1, pp. 121–122. *)
  subgroup_mul : forall g h, S g -> S h -> S (mul g h);
  (** Source for [subgroup_inv]: closure under inversion, Federer
      2.7.1, pp. 121–122. *)
  subgroup_inv : forall g, S g -> S (inv g)
}.

(** Source for [left_coset]: the cosets g G^x and h S of Federer
    2.7.1, p. 122, "maps each coset g G^x onto A(g,x)" and
    "A(g, h S) = g h S". Definition: g S = {g s : s in S}. *)
Definition left_coset (G : Type) (mul : G -> G -> G) (g : G) (S : set G) : set G :=
  [set mul g s | s in S].
