(** Federer (1969), 2.7.5, printed p. 125: "Corollary. There exist left and
    right Haar integrals of G. Proof. Taking B as the family of sets {(x,y):
    x^{-1} y in V} corresponding to all neighborhoods V of e, one sees that
    the action 2.7.2(1) of G on G is uniform. Similarly one treats the
    action 2.7.2(2) by using the sets {(x,y): x y^{-1} in V}." G is a
    locally compact Hausdorff topological group (2.7.1, p. 121), the
    standing hypothesis of section 2.7. The two actions make G a homogeneous
    space of itself (GroupMultiplicationHomogeneous.v), they are uniform
    with the printed bases (GroupUniformity.v), and G is nonempty since it
    contains e; Theorem 2.7.4 (InvariantIntegralExistence.v) then gives a
    nonzero monotone invariant integral on K(G) for each action, that is, a
    left and a right Haar integral in the sense of 2.7.2, p. 122. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import TopologicalGroupUP HomogeneousSpaceUP HaarIntegralUP
  GroupMultiplicationHomogeneous UniformActionUP GroupUniformity InvariantIntegralExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section HaarIntegralExistence.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hG : is_locally_compact_hausdorff_group mul inv e.
(** Source for [hT]: G is a topological group, Federer 2.7.1, p. 121,
    used in this section. *)
Let hT := lch_group_topological hG.

(** Source for [left_haar_integral_exists]: "There exist left ...
    Haar integrals of G", Federer 2.7.5, p. 125, from the uniformity of
    the action 2.7.2(1) and 2.7.4, p. 123. Direct formalisation. *)
Theorem left_haar_integral_exists : exists mu : (G -> R) -> R, is_left_haar_integral mul mu.
Proof.
have h := @uniform_action_invariant_integral_exists R G G mul inv e (left_multiplication_action mul)
  (topological_group_laws hT) (left_multiplication_homogeneous hT)
  (lch_group_hausdorff hG) (lch_group_locally_compact hG) (ex_intro _ e I)
  (left_multiplication_acts_uniformly hT).
exact: h.
Qed.

(** Source for [right_haar_integral_exists]: "There exist ... right
    Haar integrals of G", Federer 2.7.5, p. 125, from the uniformity of
    the action 2.7.2(2) and 2.7.4, p. 123. Direct formalisation. *)
Theorem right_haar_integral_exists : exists mu : (G -> R) -> R, is_right_haar_integral mul inv mu.
Proof.
have h := @uniform_action_invariant_integral_exists R G G mul inv e
  (right_multiplication_action mul inv)
  (topological_group_laws hT) (right_multiplication_homogeneous hT)
  (lch_group_hausdorff hG) (lch_group_locally_compact hG) (ex_intro _ e I)
  (right_multiplication_acts_uniformly hT).
exact: h.
Qed.

(** Source for [haar_integrals_exist]: "Corollary. There exist left
    and right Haar integrals of G", Federer 2.7.5, p. 125. Direct
    formalisation. *)
Corollary haar_integrals_exist :
  (exists mu : (G -> R) -> R, is_left_haar_integral mul mu) /\
  (exists mu : (G -> R) -> R, is_right_haar_integral mul inv mu).
Proof. by split; [exact: left_haar_integral_exists|exact: right_haar_integral_exists]. Qed.

End HaarIntegralExistence.
