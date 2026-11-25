(** Federer (1969), 2.7.1, printed p. 122: consequences of the specification
    of the coset space G/S in CosetSpaceUP.v. The projection pi is
    continuous; each fibre of pi is a coset g S; a map on G constant on the
    cosets factors uniquely through pi, the factor being continuous exactly
    when the map is (the universal property of G/S); pi is open; G/S is
    Hausdorff when S is closed, and locally compact when moreover G is
    locally compact. These facts are used, but not stated, in Federer's
    assertions that A^x induces a homeomorphism G/G^x ~ X and that X = G/S
    with A(g, hS) = g h S is a homogeneous space of G. Neither. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws CosetSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section CosetSpaceLaws.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hS : is_subgroup mul inv e S.
Hypothesis hQ : is_left_coset_space mul inv S pi.

(** Source for [coset_projection_continuous]: continuity of the
    projection G -> G/S for the quotient topology, supporting Federer
    2.7.1, p. 122. *)
Lemma coset_projection_continuous : continuous pi.
Proof. by apply/continuousP=> U /(coset_space_open hQ). Qed.

(** Source for [coset_projection_coset]: pi(g s) = pi(g) for s in S,
    supporting "A(g, hS) = g h S" of Federer 2.7.1, p. 122. *)
Lemma coset_projection_coset g s : S s -> pi (mul g s) = pi g.
Proof.
move=> hs; apply/esym/(coset_projection_eq hQ); rewrite (group_mulKg hG); exact: hs.
Qed.

(** Source for [coset_projection_fibre]: the fibre of pi through g is
    the coset g S, the identification of the points of G/S with cosets
    in Federer 2.7.1, p. 122. *)
Theorem coset_projection_fibre g : pi @^-1` [set pi g] = left_coset mul g S.
Proof.
apply/seteqP; split=> h /=.
- by move=> hh; apply/(left_coset_member hG); apply/(coset_projection_eq hQ).
- by move/(left_coset_member hG)=> hh; apply/esym/(coset_projection_eq hQ).
Qed.

(** Source for [coset_projection_eq_coset]: pi g = pi h if and only if
    g S = h S, for the cosets of Federer 2.7.1, p. 122. *)
Lemma coset_projection_eq_coset g h : pi g = pi h <-> left_coset mul g S = left_coset mul h S.
Proof.
have h1 := left_coset_eq hG g h hS.
have h2 := @coset_projection_eq _ _ _ _ _ _ hQ g h.
by split=> hh; [apply/h1/h2|apply/h2/h1].
Qed.

(** Source for [coset_space_factor]: a map on G which is constant on
    each coset factors through G/S, supporting "A^x induces a
    homeomorphism G/G^x ~ X" of Federer 2.7.1, p. 122. The factor is
    chosen through representatives; it does not depend on the choice. *)
Lemma coset_space_factor (Z : Type) (f : G -> Z) :
  (forall g h, S (mul (inv g) h) -> f g = f h) -> exists f' : Q -> Z, forall g, f' (pi g) = f g.
Proof.
move=> hf; exists (fun q => f (projT1 (cid (coset_projection_onto hQ q))))=> g.
case: (cid (coset_projection_onto hQ (pi g)))=> h /= hh.
by apply: hf; apply/(coset_projection_eq hQ).
Qed.

(** Source for [coset_space_factor_unique]: uniqueness of the factor
    through G/S, since pi maps onto G/S, supporting Federer 2.7.1,
    p. 122. *)
Lemma coset_space_factor_unique (Z : Type) (f1 f2 : Q -> Z) :
  (forall g, f1 (pi g) = f2 (pi g)) -> f1 = f2.
Proof.
move=> hf; apply: funext=> q; have [g <-] := coset_projection_onto hQ q; exact: hf.
Qed.

(** Source for [coset_space_factor_continuous]: a map on G/S is
    continuous exactly when its composition with pi is continuous, the
    quotient topology of G/S in Federer 2.7.1, p. 122. *)
Lemma coset_space_factor_continuous (Z : topologicalType) (f : Q -> Z) :
  continuous f <-> continuous (f \o pi).
Proof.
split=> hf.
- move=> g; apply: continuous_comp; [exact: coset_projection_continuous|exact: hf].
- apply/continuousP=> V hV; apply/(coset_space_open hQ).
  by move/continuousP: hf; apply.
Qed.

(** Source for [coset_space_universal_property]: the universal
    property of G/S used in Federer 2.7.1, p. 122: every continuous map
    f on G which is constant on the cosets g S is f' o pi for exactly
    one map f' on G/S, and f' is continuous. *)
Theorem coset_space_universal_property (Z : topologicalType) (f : G -> Z) :
  continuous f -> (forall g h, S (mul (inv g) h) -> f g = f h) ->
  exists f' : Q -> Z, [/\ continuous f', forall g, f' (pi g) = f g &
    forall f'' : Q -> Z, (forall g, f'' (pi g) = f g) -> f'' = f'].
Proof.
move=> hc hf; have [f' hf'] := coset_space_factor hf.
exists f'; split=> //.
- apply/coset_space_factor_continuous.
  by have -> : f' \o pi = f by apply: funext=> g; exact: hf'.
- by move=> f'' hf''; apply: coset_space_factor_unique=> g; rewrite hf'' hf'.
Qed.

End CosetSpaceLaws.

Section CosetSpaceTopology.
Variables G Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (S : set G) (pi : G -> Q).
Hypothesis hT : is_topological_group mul inv e.
Hypothesis hS : is_subgroup mul inv e S.
Hypothesis hQ : is_left_coset_space mul inv S pi.
(** Source for [hG]: the group laws of the topological group G,
    Federer 2.7.1, p. 121, used in this section. *)
Let hG := topological_group_laws hT.

(** Source for [coset_projection_saturation]: pi^{-1}(pi U) is the
    union of the right translates U s, s in S, supporting the
    openness of the projection G -> G/S in Federer 2.7.1, p. 122. *)
Lemma coset_projection_saturation (U : set G) :
  pi @^-1` (pi @` U) = \bigcup_(s in S) ((fun g => mul g (inv s)) @^-1` U).
Proof.
apply/seteqP; split=> g /=.
- case=> u hu /(coset_projection_eq hQ) hug; exists (mul (inv u) g)=> //=.
  by rewrite (group_invM hG) (group_invK hG) (group_mulKVg hG).
- case=> s hs /= hgs; exists (mul g (inv s))=> //; apply/(coset_projection_eq hQ).
  by rewrite (group_invM hG) (group_invK hG) (group_mulgKV hG).
Qed.

(** Source for [coset_projection_open]: the projection G -> G/S is
    an open map, supporting Federer 2.7.1, p. 122. *)
Theorem coset_projection_open : is_open_map pi.
Proof.
move=> U hU; apply/(coset_space_open hQ); rewrite coset_projection_saturation.
apply: bigcup_open=> s _; move/continuousP: (right_translation_continuous hT (inv s)); exact.
Qed.

(** Source for [coset_space_hausdorff]: the space G/S is Hausdorff
    for a closed subgroup S, supporting "one may take X = G/S" in
    Federer 2.7.1, p. 122, where X is Hausdorff. If g S differs from
    h S, then g^{-1} h lies in the open complement of S, so by the
    continuity of (a,b) |-> a^{-1} b there are open sets U containing g
    and V containing h such that a^{-1} b is not in S whenever a is in U
    and b is in V. The open sets pi(U) and pi(V) are then disjoint. *)
Theorem coset_space_hausdorff : closed S -> hausdorff_space Q.
Proof.
move=> hSc; rewrite open_hausdorff=> q1 q2 hq.
have [g hg] := coset_projection_onto hQ q1.
have [h hh] := coset_projection_onto hQ q2.
have hgh : ~ S (mul (inv g) h).
  by move=> /(coset_projection_eq hQ) hgh; move/eqP: hq; apply; rewrite -hg -hh.
pose W := (fun p : G * G => mul (inv p.1) p.2) @^-1` (~` S).
have hW : open W.
  by move/continuousP: (division_continuous hT); apply; exact: closed_openC.
have hWgh : W (g, h) by [].
move: hW; rewrite openE=> /(_ _ hWgh) [[U V] [hU hV] hUV].
exists (pi @` U°, pi @` V°)=> /=.
  by split; rewrite inE; [exists g|exists h].
split; [exact: coset_projection_open (@open_interior _ U)|exact: coset_projection_open (@open_interior _ V)|].
apply/eqP/seteqP; split; last exact: sub0set.
move=> q [[u hu <-] [v hv /esym /(coset_projection_eq hQ) huv]].
have huvW : W (u, v) by apply: hUV; exact: (conj (interior_subset hu) (interior_subset hv)).
exact: huvW huv.
Qed.

(** Source for [coset_space_locally_compact]: the space G/S is
    locally compact for a closed subgroup S of a locally compact group
    G, supporting "one may take X = G/S" in Federer 2.7.1, p. 122,
    where X is locally compact. The image under pi of a compact
    neighbourhood K of g is compact and contains the open neighbourhood
    pi(interior K) of pi(g); it is closed since G/S is Hausdorff. *)
Theorem coset_space_locally_compact :
  closed S -> locally_compact [set: G] -> locally_compact [set: Q].
Proof.
move=> hSc hl q _.
have [g <-] := coset_projection_onto hQ q.
have [K hK [hKc _]] := hl g I; rewrite withinET in hK.
have hpK : compact (pi @` K).
  apply: continuous_compact=> //; apply: continuous_subspaceT; exact: coset_projection_continuous hQ.
exists (pi @` K); last first.
  by split=> //; exact: compact_closed (coset_space_hausdorff hSc) hpK.
rewrite withinET nbhsE; exists (pi @` K°).
  split; first exact: coset_projection_open (@open_interior _ K).
  by exists g.
by move=> _ [k hk <-]; exists k=> //; exact: interior_subset.
Qed.

End CosetSpaceTopology.
