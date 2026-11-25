(** Federer (1969), 2.10.30, p. 195: the boundary-sphere exclusion after
    Steiner symmetrisation. Compact scalar sections attain their extrema; a
    symmetrised point on the containing sphere forces both original
    reflected endpoints to be present. This proves the stated exclusion on
    the entire norm sphere, which contains the boundary of the closed ball.
    No construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import InnerProductUP InnerNorm InnerMetric OrthonormalFamilies OrthogonalMaps
  UnitNormalGeometry UnitNormalTopology SteinerSymmetrisationUP CenteredSectionUP CenteredSectionLaws
  CenteredSectionBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_sphere_endpoints]: supporting
    equivalent positive form of the final assertion
    in 2.10.30, p. 195. A point of T
    on the containing sphere and its reflection
    must both belong to the original compact S. *)
Theorem steiner_sphere_endpoints (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) (r : R) :
  is_steiner_symmetrisation hB u S T -> compact S -> 0<=r ->
  (forall z, S z -> inner_norm hB z<=r) ->
  forall x, T x -> inner_norm hB x=r -> S x /\ S (normal_reflection hB u x).
Proof.
move=> hT hS hr hbound x hx hxr.
pose y := normal_foot hB u x.
pose t := inner_coordinate hB u x.
have hu := steiner_unit_normal_law hT.
have hy : inner_coordinate hB u y=0 := normal_coordinate_foot hB hu x.
have hs := steiner_normal_sections_law hT hy.
have ht : normal_scalar_section u T y t.
  by rewrite /normal_scalar_section /= /y /t normal_decomposition.
have hneT : normal_scalar_section u T y !=set0 by exists t.
have hne := (centered_section_support_law hs).2 hneT.
have hc := @normal_scalar_section_compact R V B hB u S y hu hy hS.
have hxsq : inner_norm hB y^+2+t^+2=r^+2.
  rewrite -(@normal_line_norm_square R V B hB u hu y t hy).
  by rewrite /y /t normal_decomposition hxr.
have hnorm z : normal_scalar_section u S y z -> `|z|<=`|t|.
  move=> hz.
  have hh : inner_norm hB (y+z*:u)^+2<=r^+2.
    rewrite (ler_sqr _ _) //; first exact: hbound _ hz.
    by rewrite nnegrE ?inner_norm_nonnegative.
  rewrite (@normal_line_norm_square R V B hB u hu y z hy) in hh.
  have hsq : z^+2<=t^+2 by lra.
  rewrite -(ler_sqr _ _) ?nnegrE ?normr_ge0 //.
  by rewrite -!normrX !ger0_norm ?sqr_ge0.
have [a [ha [_ hm]]] := centered_section_membership hs hne.
have habs : normal_scalar_section u T y `|t|.
  apply: (hm _).2; rewrite (ger0_norm (normr_ge0 t)); exact: (hm t).1 ht.
have he := @centered_section_boundary_endpoints R (normal_scalar_section u S y)
  (normal_scalar_section u T y) `|t| hs hc (normr_ge0 t) hnorm habs.
have hp : normal_scalar_section u S y t /\ normal_scalar_section u S y (-t).
  case: (leP 0 t)=> ht0.
  - rewrite (ger0_norm ht0) in he; exact (conj he.2 he.1).
  - by rewrite (ltr0_norm ht0) opprK in he.
move: hp=> [h1 h2]; split.
- by move: h1; rewrite /normal_scalar_section /= /y /t normal_decomposition.
- have her : y+(-t)*:u=normal_reflection hB u x.
    rewrite /y /t -(@normal_reflection_coordinate R V B hB u hu x)
      -(@normal_reflection_foot R V B hB u hu x).
    exact: normal_decomposition.
  by move: h2; rewrite /normal_scalar_section /= her.
Qed.

(** Source for [steiner_sphere_exclusion]: direct final
    inclusion (Z minus S) union rho_u(Z minus S)
    contained in Z minus T in 2.10.30,
    p. 195, with Z the whole norm sphere.
    This stronger sphere version also covers radius zero. *)
Theorem steiner_sphere_exclusion (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) (r : R) :
  is_steiner_symmetrisation hB u S T -> compact S -> 0<=r ->
  (forall z, S z -> inner_norm hB z<=r) ->
  let Z := [set x | inner_norm hB x=r] in
  (Z `\` S) `|` (normal_reflection hB u @` (Z `\` S)) `<=` Z `\` T.
Proof.
move=> hT hS hr hbound Z.
have hu := steiner_unit_normal_law hT.
have hn x : inner_norm hB (normal_reflection hB u x)=inner_norm hB x.
  exact (@orthogonal_map_norm R V V B B hB hB
    (GRing.Linear.clone _ _ _ _ (normal_reflection hB u) _)
    (@normal_reflection_orthogonal R V B hB u hu) x).
move=> x [[hx hxS]|[y [hy hyS] <-]].
- split=> // hxT; exact: hxS (steiner_sphere_endpoints hT hS hr hbound hxT hx).1.
- split; first by change (inner_norm hB (normal_reflection hB u y)=r); rewrite hn.
  move=> hxT.
  have hx : inner_norm hB (normal_reflection hB u y)=r by rewrite hn.
  have hh := (steiner_sphere_endpoints hT hS hr hbound hxT hx).2.
  apply: hyS; by rewrite (@normal_reflectionK R V B hB u hu y) in hh.
Qed.
