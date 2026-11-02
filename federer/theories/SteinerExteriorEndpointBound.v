(** Original endpoint families and their norm comparison in Federer (1969),
    2.10.32, pp. 196–197. The original pairs are chosen by the proved
    compact-convex section laws. No global selection operation or additional
    axiom is exposed. The subsequent exterior estimate uses the corrected
    normalising factor from the erratum cited in NormalExteriorNormBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex OrthonormalFamilies UnitNormalGeometry
  SteinerSymmetrisationUP SteinerConvexChordRealisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_original_endpoint_choices]: direct
    simultaneous choices gamma_i and delta_i
    for the four displayed original points in
    2.10.32, p. 196. The proof works for
    any index type; the application uses n indices. *)
Theorem steiner_original_endpoint_choices (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (I : Type) (u : V) (S T : set (inner_metric_space hB)) (x y : I -> V) :
  is_steiner_symmetrisation hB u S T -> compact S -> is_inner_convex S ->
  (forall i, T (x i)) -> (forall i, T (y i)) ->
  exists g d : I -> R, forall i,
    S (normal_foot hB u (x i)+g i*:u) /\
    S (normal_foot hB u (x i)+(g i+2*inner_coordinate hB u (x i))*:u) /\
    S (normal_foot hB u (y i)+d i*:u) /\
    S (normal_foot hB u (y i)+(d i+2*inner_coordinate hB u (y i))*:u).
Proof.
move=> hs hc hconv hx hy.
have hg i := steiner_compact_convex_point_chord hs hc hconv (hx i).
have hd i := steiner_compact_convex_point_chord hs hc hconv (hy i).
pose g i := projT1 (cid (hg i)).
pose d i := projT1 (cid (hd i)).
exists g,d=> i.
have hgi := projT2 (cid (hg i)); have hdi := projT2 (cid (hd i)).
exact (conj hgi.1 (conj hgi.2 hdi)).
Qed.
