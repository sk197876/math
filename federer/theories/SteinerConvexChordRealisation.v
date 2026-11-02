(** Original endpoint choices for the Steiner estimate in Federer (1969),
    2.10.32, p. 196. Apply the scalar compact-convex chord lemma to each
    normal line using only the symmetrisation specification. The resulting
    points are the printed a'_i,a''_i and b'_i,b''_i, before their exterior
    products are compared on pp. 196–197. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex OrthonormalFamilies
  UnitNormalGeometry UnitNormalTopology SteinerSymmetrisationUP SteinerSymmetrisationLaws
  NormalSectionConvex CenteredSectionChordRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_compact_convex_section_chord]: direct
    supporting normal-line endpoint choices in
    2.10.32, p. 196. Compactness and convexity
    of S supply both original endpoints at scalar
    separation 2 alpha. No finite dimension is needed. *)
Theorem steiner_compact_convex_section_chord (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u y : V) (S T : set (inner_metric_space hB)) (alpha : R) :
  is_steiner_symmetrisation hB u S T -> compact S -> is_inner_convex S ->
  inner_coordinate hB u y=0 -> T (y+alpha*:u) ->
  exists gamma : R, S (y+gamma*:u) /\ S (y+(gamma+2*alpha)*:u).
Proof.
move=> hs hc hconv hy halpha.
have hu := steiner_unit_normal_law hs.
have hsection := steiner_normal_sections_law hs hy.
have hcompact := @normal_scalar_section_compact R V B hB u S y hu hy hc.
have hcv := @normal_scalar_section_convex R V u y S hconv.
exact (centered_compact_convex_section_chord hsection hcompact hcv halpha).
Qed.

(** Source for [steiner_compact_convex_point_chord]: direct
    endpoint choices for a given a_i in T
    in 2.10.32, p. 196. Its orthogonal
    foot is v_i and its normal coordinate is
    alpha_i; both source points share that foot. *)
Theorem steiner_compact_convex_point_chord (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) (x : V) :
  is_steiner_symmetrisation hB u S T -> compact S -> is_inner_convex S -> T x ->
  exists gamma : R,
    S (normal_foot hB u x+gamma*:u) /\
    S (normal_foot hB u x+(gamma+2*inner_coordinate hB u x)*:u).
Proof.
move=> hs hc hconv hx.
have hu := steiner_unit_normal_law hs.
have hy := normal_coordinate_foot hB hu x.
have hline : T (normal_foot hB u x+inner_coordinate hB u x*:u).
  by rewrite normal_decomposition.
exact (steiner_compact_convex_section_chord hs hc hconv hy hline).
Qed.
