(** Federer (1969), 2.7.2, printed p. 123: "These two cases are related by
    the commutative diagram G --(left multiplication by g)--> G p | | p G
    --(right multiplication by g^{-1})--> G where p(x) = x^{-1} for x in G.
    We see that mu is a left chi covariant integral if and only if p#(mu) is
    a right chi covariant integral." Here p is the inversion inv of the
    topological group G, a homeomorphism equal to its own inverse, and p# is
    daniell_pushforward of 2.5.19, p. 113. The diagram is the identity
    (gx)^{-1} = x^{-1}g^{-1}; the equivalence is the general fact of
    EquivariantPushforward.v. The symmetric statement, with the roles of the
    two actions exchanged, and the corresponding statements for invariant
    integrals and Haar integrals are added; they follow in the same way.
    Only the group laws and the continuity of the inversion are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  DaniellSpacePushforward CovariantIntegralUP HaarIntegralUP EquivariantPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarInversion.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hT : is_topological_group mul inv e.
(** Source for [hG]: the group laws of G, Federer 2.7.1, p. 121, used
    in this section. *)
Let hG := topological_group_laws hT.
(** Source for [hp]: "p(x) = x^{-1} for x in G", Federer 2.7.2,
    p. 123, is a homeomorphism with inverse p. *)
Let hp : is_homeomorphism_with_inverse inv inv := inversion_homeomorphism hT.

(** Source for [inversion_commutative_diagram]: the commutative
    diagram of Federer 2.7.2, p. 123: p followed after left
    multiplication by g equals right multiplication by g^{-1} followed
    after p, that is (gx)^{-1} = x^{-1}g^{-1}. Direct formalisation. *)
Lemma inversion_commutative_diagram g :
  inv \o left_multiplication_action mul g = right_multiplication_action mul inv g \o inv.
Proof.
apply: funext=> x.
by rewrite /= /left_multiplication_action /right_multiplication_action (group_invM hG).
Qed.

(** Source for [inversion_intertwines_left_right]: the pointwise form
    of the commutative diagram of Federer 2.7.2, p. 123. Supporting
    lemma. *)
Lemma inversion_intertwines_left_right g x :
  inv (left_multiplication_action mul g x) = right_multiplication_action mul inv g (inv x).
Proof. by have := congr1 (fun f => f x) (inversion_commutative_diagram g). Qed.

(** Source for [inversion_intertwines_right_left]: the diagram of
    Federer 2.7.2, p. 123, read upwards: (xg^{-1})^{-1} = g x^{-1}.
    Supporting lemma for the symmetric statement. *)
Lemma inversion_intertwines_right_left g x :
  inv (right_multiplication_action mul inv g x) = left_multiplication_action mul g (inv x).
Proof.
by rewrite /left_multiplication_action /right_multiplication_action (group_invM hG) (group_invK hG).
Qed.

(** Source for [left_covariant_inversion]: "We see that mu is a left
    chi covariant integral if and only if p#(mu) is a right chi
    covariant integral", Federer 2.7.2, p. 123. Direct formalisation. *)
Theorem left_covariant_inversion (chi : G -> R) (mu : (G -> R) -> R) :
  is_left_covariant_integral mul chi mu <->
  is_right_covariant_integral mul inv chi (daniell_pushforward inv mu).
Proof. exact: (equivariant_covariant_integral hp inversion_intertwines_left_right). Qed.

(** Source for [right_covariant_inversion]: the statement of Federer
    2.7.2, p. 123, with the two actions exchanged: mu is a right chi
    covariant integral if and only if p#(mu) is a left chi covariant
    integral. Supporting theorem. *)
Theorem right_covariant_inversion (chi : G -> R) (mu : (G -> R) -> R) :
  is_right_covariant_integral mul inv chi mu <->
  is_left_covariant_integral mul chi (daniell_pushforward inv mu).
Proof. exact: (equivariant_covariant_integral hp inversion_intertwines_right_left). Qed.

(** Source for [left_invariant_inversion]: the case chi = 1 of
    Federer 2.7.2, p. 123: mu is a left invariant integral if and only
    if p#(mu) is a right invariant integral. *)
Corollary left_invariant_inversion (mu : (G -> R) -> R) :
  is_left_invariant_integral mul mu <-> is_right_invariant_integral mul inv (daniell_pushforward inv mu).
Proof. exact: left_covariant_inversion. Qed.

(** Source for [left_haar_inversion]: the relation of Federer 2.7.2,
    p. 123, for the Haar integrals of p. 122: mu is a left Haar integral
    of G if and only if p#(mu) is a right Haar integral of G. Supporting
    theorem. *)
Theorem left_haar_inversion (mu : (G -> R) -> R) :
  is_left_haar_integral mul mu <-> is_right_haar_integral mul inv (daniell_pushforward inv mu).
Proof. exact: (equivariant_nonzero_invariant_integral hp inversion_intertwines_left_right). Qed.

(** Source for [right_haar_inversion]: the relation of Federer 2.7.2,
    p. 123, with the two actions exchanged: mu is a right Haar integral
    of G if and only if p#(mu) is a left Haar integral of G. Supporting
    theorem. *)
Theorem right_haar_inversion (mu : (G -> R) -> R) :
  is_right_haar_integral mul inv mu <-> is_left_haar_integral mul (daniell_pushforward inv mu).
Proof. exact: (equivariant_nonzero_invariant_integral hp inversion_intertwines_right_left). Qed.

End HaarInversion.
