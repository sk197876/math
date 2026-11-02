(** Final line-section argument of Federer (1969), 2.10.31, p. 196. A
    minimal-radius class member fills every radial segment of its containing
    ball. A missing point would give the strict line-length inequality in
    the book; instead express its contrapositive using the proved compact
    scalar full-length lemma. The symmetrised class member has the full
    sphere by the preceding cap proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear InnerProductUP InnerProductLaws InnerNorm InnerMetric
  OrthonormalFamilies UnitNormalGeometry UnitNormalTopology CompactSetDistanceProfile
  CompactHausdorffMetric CompactEnclosingRadius LipschitzFunctionCompact
  SteinerStableFamilyUP SteinerSymmetrisationUP SteinerBallBounds SteinerMinimalSphere
  CenteredSectionFullInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_minimal_radius_radial_segment]: supporting
    contrapositive of the final strict chord inequality
    in 2.10.31, p. 196. For any unit
    normal u the whole segment [-r,r]u belongs
    to the original minimal-radius member S. *)
Theorem steiner_minimal_radius_radial_segment (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB)) (r : R) (u : V) :
  metric_boundedly_compact (inner_metric_space hB) ->
  is_steiner_stable_family hB C -> C S -> 0<=r ->
  (forall T, C T -> r<=compact_enclosing_radius (0 : inner_metric_space hB) T) ->
  (forall x, val S x -> inner_norm hB x<=r) -> B u u= 1 ->
  forall t, `|t|<=r -> val S (t*:u).
Proof.
move=> hX hC hS hr hmin hb hu t ht.
have [T [hT hs]] := hC S hS u hu.
have hTb := steiner_preserves_centered_ball hs hr hb.
have h0 : inner_coordinate hB u 0=0.
  by rewrite inner_coordinateE (bil0l (inner_bilinear hB)).
have hsection := steiner_normal_sections_law hs h0.
have hcompact := @normal_scalar_section_compact R V B hB u (val S) 0 hu h0 (set_valP S).1.
have hun : inner_norm hB u= 1 := unit_normal_norm hB hu.
have hbound z : normal_scalar_section u (val S) 0 z -> `|z|<=r.
  move=> hz; have hh := hb _ hz.
  by rewrite add0r inner_normZ hun mulr1 in hh.
have hrnorm : inner_norm hB (r*:u)=r.
  by rewrite inner_normZ hun mulr1 ger0_norm.
have hpoint := steiner_minimal_radius_contains_sphere hX hC hT hr hmin hTb hrnorm.
have hBr : normal_scalar_section u (val T) 0 r by rewrite /normal_scalar_section /= add0r.
have hh := centered_section_full_interval hsection hcompact hr hbound hBr ht.
by move: hh; rewrite /normal_scalar_section /= add0r.
Qed.
