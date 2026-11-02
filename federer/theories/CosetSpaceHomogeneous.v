(** Federer (1969), 2.7.1, printed p. 122: "Every closed subgroup S of G is
    the isotropy subgroup for some such action A, because one may take X =
    G/S and A(g, hS) = g h S whenever g, h in G; then G^S = S." The action
    is specified by the displayed law A(g, pi h) = pi(g h), where pi: G ->
    G/S is the projection of CosetSpaceUP.v; such an action exists and is
    unique. For a closed subgroup S of a locally compact topological group
    G, the space G/S is locally compact and Hausdorff (CosetSpaceLaws.v),
    and it is a homogeneous space of G through A: A is continuous because pi
    is open and the multiplication is continuous, the compatibility law is
    associativity, and the orbit maps g |-> pi(g h) are open and onto. The
    isotropy subgroup of the point S = pi(e) is S. The Hausdorff property of
    G, assumed by Federer, is not needed. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP CosetSpaceUP CosetSpaceLaws CosetSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_coset_action]: "A(g, hS) = g h S whenever g, h in
    G", Federer 2.7.1, p. 122. Definition of the action of G on G/S by
    its law on the cosets pi h = h S. *)
Definition is_coset_action (G Q : Type) (mul : G -> G -> G) (pi : G -> Q) (A : G -> Q -> Q) :=
  forall g h, A g (pi h) = pi (mul g h).

Section CosetAction.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hQ : is_left_coset_space mul inv S pi.

(** Source for [coset_action_exists]: the formula A(g, hS) = g h S of
    Federer 2.7.1, p. 122, defines an action: pi(g h) depends only on
    the coset h S. Existence. *)
Lemma coset_action_exists : exists A : G -> Q -> Q, is_coset_action mul pi A.
Proof.
exists (fun g q => pi (mul g (projT1 (cid (coset_projection_onto hQ q))))).
move=> g h; case: (cid (coset_projection_onto hQ (pi h)))=> k /= /(coset_projection_eq hQ) hkh.
by apply/(coset_projection_eq hQ); rewrite (group_invM hG) -(group_mulA hG) (group_mulKg hG).
Qed.

(** Source for [coset_action_unique]: the formula A(g, hS) = g h S of
    Federer 2.7.1, p. 122, determines A, since every point of G/S is a
    coset. *)
Lemma coset_action_unique (A1 A2 : G -> Q -> Q) :
  is_coset_action mul pi A1 -> is_coset_action mul pi A2 -> A1 = A2.
Proof.
move=> h1 h2; apply: funext=> g; apply: funext=> q.
by have [h <-] := coset_projection_onto hQ q; rewrite h1 h2.
Qed.

(** Source for [coset_action_isotropy]: "then G^S = S", Federer 2.7.1,
    p. 122, for the point S = pi(e) of G/S. Direct formalisation. *)
Theorem coset_action_isotropy (A : G -> Q -> Q) :
  is_subgroup mul inv e S -> is_coset_action mul pi A -> isotropy_subgroup A (pi e) = S.
Proof.
move=> hS hA; apply/seteqP; split=> g; rewrite /isotropy_subgroup /= hA (group_mulg1 hG).
- move=> /(coset_projection_eq hQ); rewrite (group_mulg1 hG)=> hg.
  by rewrite -(group_invK hG g); exact: (subgroup_inv hS).
- move=> hg; apply/(coset_projection_eq hQ); rewrite (group_mulg1 hG); exact: (subgroup_inv hS).
Qed.

End CosetAction.

Section CosetHomogeneous.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hS : is_subgroup mul inv e S.
Hypothesis hQ : is_left_coset_space mul inv S pi.
(** Source for [hG]: the group laws of the topological group G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hG := topological_group_laws hT.

(** Source for [coset_action_continuous]: continuity of
    A: G x G/S -> G/S, part of "one may take X = G/S", Federer 2.7.1,
    p. 122. If W is a neighbourhood of pi(g h), the continuity of the
    multiplication gives neighbourhoods U of g and V of h with
    pi(u v) in W for u in U, v in V; then U x pi(interior V) is a
    neighbourhood of (g, pi h), since pi is open. *)
Lemma coset_action_continuous (A : G -> Q -> Q) :
  is_coset_action mul pi A -> continuous (fun p : G * Q => A p.1 p.2).
Proof.
move=> hA [g q]; have [h <-] := coset_projection_onto hQ q.
move=> W /=; rewrite hA=> hW.
have hpW := @coset_projection_continuous _ _ _ _ _ _ hQ (mul g h) W hW.
have hm : continuous (fun p : G * G => mul p.1 p.2) := topological_group_mul_continuous hT.
have [[U V] [hU hV] hUV] := @hm (g, h) _ hpW.
exists (U, pi @` V°); first split=> //=.
  apply: open_nbhs_nbhs; split; first exact: coset_projection_open hT hQ _ (@open_interior _ V).
  by exists h.
move=> [a b] [/= ha [v hv <-]]; rewrite /= hA.
by apply: (hUV (a, v)); split=> //; exact: interior_subset.
Qed.

(** Source for [coset_action_homogeneous]: "one may take X = G/S and
    A(g, hS) = g h S whenever g, h in G", Federer 2.7.1, p. 122: G/S is
    a homogeneous space of G through A. Direct formalisation. *)
Theorem coset_action_homogeneous (A : G -> Q -> Q) :
  is_coset_action mul pi A -> is_homogeneous_space mul A.
Proof.
move=> hA; constructor.
- exact: coset_action_continuous.
- move=> g h q; have [k <-] := coset_projection_onto hQ q.
  by rewrite !hA (group_mulA hG).
- move=> q U hU; have [k <-] := coset_projection_onto hQ q.
  have -> : orbit_map A (pi k) @` U = pi @` ((fun g => mul g k) @` U).
    apply/seteqP; split=> y.
    + by case=> g hg <-; exists (mul g k); [exists g|rewrite /orbit_map hA].
    + by case=> _ [g hg <-] <-; exists g=> //; rewrite /orbit_map hA.
  apply: (coset_projection_open hT hQ); exact: right_translation_open_map hT k U hU.
- move=> q; have [k <-] := coset_projection_onto hQ q.
  apply/seteqP; split=> // y _; have [h <-] := coset_projection_onto hQ y.
  by exists (mul h (inv k))=> //; rewrite /orbit_map hA (group_mulgKV hG).
Qed.

(** Source for [closed_subgroup_coset_homogeneous]: "Every closed
    subgroup S of G is the isotropy subgroup for some such action A,
    because one may take X = G/S and A(g, hS) = g h S whenever g, h in
    G; then G^S = S", Federer 2.7.1, p. 122. For a closed subgroup S of
    a locally compact topological group G, every space G/S with its
    action A is locally compact, Hausdorff and homogeneous, and the
    isotropy subgroup of S = pi(e) is S. Direct formalisation; the
    Hausdorff property of G is not used. *)
Theorem closed_subgroup_coset_homogeneous (A : G -> Q -> Q) :
  closed S -> locally_compact [set: G] -> is_coset_action mul pi A ->
  [/\ hausdorff_space Q, locally_compact [set: Q], is_homogeneous_space mul A &
    isotropy_subgroup A (pi e) = S].
Proof.
move=> hSc hl hA; split.
- exact: coset_space_hausdorff hT hQ hSc.
- exact: coset_space_locally_compact hT hQ hSc hl.
- exact: coset_action_homogeneous.
- exact: coset_action_isotropy hG hQ A hS hA.
Qed.

End CosetHomogeneous.

(** Source for [closed_subgroup_isotropy]: "Every closed subgroup S of
    G is the isotropy subgroup for some such action A", Federer 2.7.1,
    p. 122: there are a locally compact Hausdorff space X, namely the
    sealed coset space G/S, an action A making X a homogeneous space of
    G, and a point x of X with G^x = S. Direct formalisation. *)
Theorem closed_subgroup_isotropy (G : topologicalType) (mul : G -> G -> G) (inv : G -> G) (e : G)
    (S : set G) :
  is_topological_group mul inv e -> locally_compact [set: G] ->
  is_subgroup mul inv e S -> closed S ->
  exists (X : topologicalType) (A : G -> X -> X) (x : X),
    [/\ hausdorff_space X, locally_compact [set: X], is_homogeneous_space mul A &
      isotropy_subgroup A x = S].
Proof.
move=> hT hl hS hSc.
have hQ := coset_space_specification (topological_group_laws hT) hS.
have [A hA] := coset_action_exists (topological_group_laws hT) hQ.
exists (coset_space mul S), A, (coset_projection mul S e).
by have := closed_subgroup_coset_homogeneous hT hS hQ hSc hl hA.
Qed.
