(** Federer (1969), 2.7.1, printed pp. 121–122: "It follows that for each g
    in G the map A_g: X -> X, A_g(x) = A(g,x) whenever x in X, is a
    homeomorphism, with (A_g)^{-1} = A_{g^{-1}} and A_e = 1_X, where e is
    the identity of G. Moreover, for each x in X the isotropy subgroup G^x =
    G cap {g: A(g,x) = x} is closed in G". Here A_g is the curried map A g.
    The identity A_e = 1_X is derived from the compatibility of A with the
    multiplication and from im A^x = X, as Federer's "It follows" requires;
    the group laws and the continuity of A suffice, and the closedness of
    G^x uses that points of the Hausdorff space X are closed. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TopologicalProductMaps HomeomorphismUP TopologicalGroupUP
  TopologicalGroupLaws HomogeneousSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section HomogeneousSpaceLaws.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.

(** Source for [homogeneous_transitive]: transitivity of the action,
    Federer 2.7.1, p. 121, "the transitive left action A", from
    im A^x = X. *)
Lemma homogeneous_transitive x y : exists g, A g x = y.
Proof.
have : (orbit_map A x @` setT) y by rewrite (homogeneous_orbit_onto hA x).
by case=> g _ hg; exists g.
Qed.

(** Source for [homogeneous_unit_action]: A(e,x) = x, the pointwise
    form of "A_e = 1_X" in Federer 2.7.1, p. 121. If A(g,x) = x, then
    A(e,x) = A(e,A(g,x)) = A(eg,x) = A(g,x) = x; such g exists because
    im A^x = X. Direct formalisation. *)
Lemma homogeneous_unit_action x : A e x = x.
Proof.
have [g hg] := homogeneous_transitive x x.
by rewrite -hg -(homogeneous_action_compatible hA) (group_mul1g hG).
Qed.

(** Source for [homogeneous_unit_identity]: "A_e = 1_X", Federer
    2.7.1, p. 121. Direct formalisation. *)
Lemma homogeneous_unit_identity : A e = id.
Proof. by apply: funext=> x; exact: homogeneous_unit_action. Qed.

(** Source for [homogeneous_translation_inverse_left]: A_{g^{-1}} o A_g
    = 1_X, part of "(A_g)^{-1} = A_{g^{-1}}" in Federer 2.7.1,
    p. 121. *)
Lemma homogeneous_translation_inverse_left g : cancel (A g) (A (inv g)).
Proof.
by move=> x; rewrite -(homogeneous_action_compatible hA) (group_mulVg hG) homogeneous_unit_action.
Qed.

(** Source for [homogeneous_translation_inverse_right]: A_g o
    A_{g^{-1}} = 1_X, part of "(A_g)^{-1} = A_{g^{-1}}" in Federer
    2.7.1, p. 121. *)
Lemma homogeneous_translation_inverse_right g : cancel (A (inv g)) (A g).
Proof.
by move=> x; rewrite -(homogeneous_action_compatible hA) (group_mulgV hG) homogeneous_unit_action.
Qed.

(** Source for [homogeneous_translation_continuous]: continuity of
    A_g, Federer 2.7.1, p. 121, from the continuity of A on G x X. *)
Lemma homogeneous_translation_continuous g : continuous (A g).
Proof.
have hp : continuous (fun x : X => (g, x)).
  by apply: topological_pair_continuous; [exact: cst_continuous|move=> ?].
have hc : continuous (fun p : G * X => A p.1 p.2) := homogeneous_action_continuous hA.
by move=> x; have := continuous_comp (hp x) (@hc (g, x)); exact.
Qed.

(** Source for [homogeneous_translation_homeomorphism]: "for each g
    in G the map A_g: X -> X ... is a homeomorphism, with
    (A_g)^{-1} = A_{g^{-1}}", Federer 2.7.1, p. 121. Direct
    formalisation. *)
Theorem homogeneous_translation_homeomorphism g :
  is_homeomorphism_with_inverse (A g) (A (inv g)).
Proof.
constructor; [exact: homogeneous_translation_continuous|exact: homogeneous_translation_continuous| |].
- exact: homogeneous_translation_inverse_left.
- exact: homogeneous_translation_inverse_right.
Qed.

(** Source for [orbit_map_continuous]: continuity of A^x, supporting
    the homeomorphism G/G^x ~ X of Federer 2.7.1, p. 122. *)
Lemma orbit_map_continuous x : continuous (orbit_map A x).
Proof.
have hp : continuous (fun g : G => (g, x)).
  by apply: topological_pair_continuous; [move=> ?|exact: cst_continuous].
have hc : continuous (fun p : G * X => A p.1 p.2) := homogeneous_action_continuous hA.
by move=> g; have := continuous_comp (hp g) (@hc (g, x)); exact.
Qed.

(** Source for [orbit_map_eq]: A(g,x) = A(h,x) if and only if
    g^{-1} h belongs to G^x, supporting "A^x induces a homeomorphism
    G/G^x ~ X, which maps each coset g G^x onto A(g,x)", Federer 2.7.1,
    p. 122. *)
Lemma orbit_map_eq x g h : A g x = A h x <-> isotropy_subgroup A x (mul (inv g) h).
Proof.
rewrite /isotropy_subgroup /= (homogeneous_action_compatible hA); split.
- by move=> <-; rewrite homogeneous_translation_inverse_left.
- move=> hgh; rewrite -[in RHS](group_mulKVg hG g h) !(homogeneous_action_compatible hA).
  by rewrite hgh.
Qed.

(** Source for [isotropy_subgroup_subgroup]: "the isotropy subgroup
    G^x", Federer 2.7.1, p. 121: G^x is a subgroup of G. *)
Theorem isotropy_subgroup_subgroup x : is_subgroup mul inv e (isotropy_subgroup A x).
Proof.
constructor; rewrite /isotropy_subgroup /=.
- exact: homogeneous_unit_action.
- by move=> g h hg hh; rewrite (homogeneous_action_compatible hA) hh hg.
- by move=> g hg; rewrite -[in LHS]hg homogeneous_translation_inverse_left.
Qed.

(** Source for [isotropy_subgroup_closed]: "the isotropy subgroup G^x
    ... is closed in G", Federer 2.7.1, pp. 121–122. The set G^x is
    the inverse image of the closed set {x} of the Hausdorff space X
    under the continuous map A^x. Direct formalisation. *)
Theorem isotropy_subgroup_closed x : hausdorff_space X -> closed (isotropy_subgroup A x).
Proof.
move=> hX; have hx : closed [set x] by exact: accessible_closed_set1 (hausdorff_accessible hX) x.
have -> : isotropy_subgroup A x = orbit_map A x @^-1` [set x] by [].
apply: preimage_closed hx=> g _; exact: orbit_map_continuous.
Qed.

End HomogeneousSpaceLaws.

Arguments homogeneous_translation_continuous [G X mul A] hA g _ _ _.
Arguments orbit_map_continuous [G X mul A] hA x _ _ _.
