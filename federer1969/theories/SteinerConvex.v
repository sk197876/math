(** Federer (1969), 2.10.30, p. 195: convex S has convex Steiner
    symmetrisation T. The proof uses bounded scalar convex sections, their
    actual interval lengths, and the abstract centred-section laws.
    Compactness is not assumed. Source context and the absence of a
    separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies InnerConvex
  RealMetricBackground CoveringFamilyUP UnitNormalGeometry UnitNormalMetric
  NormalSectionConvex CenteredSectionUP CenteredSectionMinkowski SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_preserves_convexity]: direct
    convexity conclusion in 2.10.30, p. 195,
    for bounded S as in the definition of the
    operation. Nonclosed convex sets and degenerate
    normal sections are included. *)
Theorem steiner_preserves_convexity (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) :
  is_steiner_symmetrisation hB u S T -> metric_set_bounded S ->
  is_inner_convex S -> is_inner_convex T.
Proof.
move=> hT hb hS x y hx hy t ht0 ht1.
pose p := normal_foot hB u x.
pose q := normal_foot hB u y.
pose w := (1-t)*:p+t*:q.
pose a := inner_coordinate hB u x.
pose b := inner_coordinate hB u y.
have hu := steiner_unit_normal_law hT.
have hp : inner_coordinate hB u p=0 := normal_coordinate_foot hB hu x.
have hq : inner_coordinate hB u q=0 := normal_coordinate_foot hB hu y.
have hw : inner_coordinate hB u w=0.
  rewrite /w linearD !linearZ hp hq.
  change ((1-t)*0+t*0=0); by rewrite !mulr0 add0r.
have hsecP := steiner_normal_sections_law hT hp.
have hsecQ := steiner_normal_sections_law hT hq.
have hsecW := steiner_normal_sections_law hT hw.
have ha : normal_scalar_section u T p a.
  by rewrite /normal_scalar_section /= /p /a normal_decomposition.
have hb0 : normal_scalar_section u T q b.
  by rewrite /normal_scalar_section /= /q /b normal_decomposition.
have h1t : 0<=1-t by rewrite subr_ge0.
have hmid := @centered_section_minkowski_inclusion R
  (normal_scalar_section u S p) (normal_scalar_section u S q) (normal_scalar_section u S w)
  (normal_scalar_section u T p) (normal_scalar_section u T q) (normal_scalar_section u T w)
  (1-t) t hsecP hsecQ hsecW
  (@normal_scalar_section_convex R V u p S hS)
  (@normal_scalar_section_convex R V u q S hS)
  (@normal_scalar_section_convex R V u w S hS)
  (@normal_sections_bounded R V B hB u hu S hb p)
  (@normal_sections_bounded R V B hB u hu S hb q)
  (@normal_sections_bounded R V B hB u hu S hb w) h1t ht0
  (@normal_section_minkowski_inclusion R V u p q S t hS ht0 ht1) a b ha hb0.
have he : w+((1-t)*a+t*b)*:u=(1-t)*:x+t*:y.
  rewrite /w -normal_section_convex_combination.
  by rewrite /p /q /a /b !normal_decomposition.
by move: hmid; rewrite /normal_scalar_section /= he.
Qed.
