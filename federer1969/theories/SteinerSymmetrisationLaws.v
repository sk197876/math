(** Basic consequences of the line-section definition in Federer (1969),
    2.10.30, p. 195. Derive uniqueness and reflection symmetry without using
    any construction. Source context: SteinerSymmetrisationUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import InnerProductUP OrthonormalFamilies RealMetricBackground
  CenteredSectionUP CenteredSectionLaws UnitNormalGeometry SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SteinerLaws.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable u : V.
Variables S T : set V.
Hypothesis hT : is_steiner_symmetrisation hB u S T.
Local Notation c := (inner_coordinate hB u).
Local Notation hu := (steiner_unit_normal_law hT).

(** Source for [steiner_point_section]: supporting
    intrinsic membership on the normal line through x
    in 2.10.30, p. 195. The foot lies in
    the hyperplane by the already proved projection laws. *)
Lemma steiner_point_section x :
  T x <-> normal_scalar_section u T (normal_foot hB u x) (c x).
Proof. by rewrite /normal_scalar_section /= normal_decomposition. Qed.

(** Source for [steiner_symmetrisation_unique]: supporting
    uniqueness of the operation specified in 2.10.30,
    p. 195. Uniqueness on every normal line gives
    equality on the whole inner-product space. *)
Theorem steiner_symmetrisation_unique (U : set V) :
  is_steiner_symmetrisation hB u S U -> T=U.
Proof.
move=> hU; apply/seteqP; split=> x hx.
- have he := centered_section_unique
    (steiner_normal_sections_law hT (normal_coordinate_foot hB hu x))
    (steiner_normal_sections_law hU (normal_coordinate_foot hB hu x)).
  have ht : normal_scalar_section u T (normal_foot hB u x) (c x).
    by rewrite /normal_scalar_section /= normal_decomposition.
  rewrite he /normal_scalar_section /= normal_decomposition in ht; exact ht.
- have he := centered_section_unique
    (steiner_normal_sections_law hT (normal_coordinate_foot hB hu x))
    (steiner_normal_sections_law hU (normal_coordinate_foot hB hu x)).
  have ht : normal_scalar_section u U (normal_foot hB u x) (c x).
    by rewrite /normal_scalar_section /= normal_decomposition.
  rewrite -he /normal_scalar_section /= normal_decomposition in ht; exact ht.
Qed.

(** Source for [steiner_reflection_membership]: direct reflection invariance
    of T in 2.10.30, p. 195, first expressed pointwise. *)
Lemma steiner_reflection_membership x :
  T (normal_reflection hB u x) <-> T x.
Proof.
have hs := steiner_normal_sections_law hT (normal_coordinate_foot hB hu x).
have he := centered_section_reflection hs (c x).
rewrite /normal_scalar_section /= in he.
have h1 : normal_foot hB u x+(-c x)*:u=normal_reflection hB u x.
  rewrite /normal_foot /normal_reflection scaleNr -addrA -opprD -scalerDl.
  congr (x-_); congr (_*:u); ring.
have h2 := normal_decomposition hB u x.
by rewrite h1 h2 in he.
Qed.

(** Source for [steiner_reflection_image]: direct
    rho_u(T)=T in 2.10.30, p. 195, including
    the empty set and zero-length sections. *)
Theorem steiner_reflection_image : normal_reflection hB u @` T=T.
Proof.
apply/seteqP; split=> x.
- move=> [y hy <-]; exact: (steiner_reflection_membership y).2 hy.
- move=> hx; exists (normal_reflection hB u x).
  + exact: (steiner_reflection_membership x).2 hx.
  + exact (normal_reflectionK hB hu x).
Qed.

(** Source for [steiner_projection_support]: direct
    preservation of nonempty normal sections in 2.10.30,
    p. 195. This support property is distinct from
    positive section length. *)
Lemma steiner_projection_support y : c y=0 ->
  normal_scalar_section u S y !=set0 <-> normal_scalar_section u T y !=set0.
Proof. move=> hy; exact: centered_section_support_law (steiner_normal_sections_law hT hy). Qed.
End SteinerLaws.
