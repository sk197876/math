(** Private existence proof for Federer (1969), 2.10.30, p. 195. Glue the
    already specified, proved and sealed centred scalar sections along all
    normal lines. This witness is hidden by SteinerSymmetrisationSealed.v;
    downstream theorems use only the line-section specification. Source
    editions: SteinerSymmetrisationUP.v *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies RealMetricBackground
  CoveringFamilyUP CenteredSectionUP CenteredSection UnitNormalGeometry UnitNormalMetric
  SteinerSymmetrisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_symmetrisation_exists]: supporting
    existence of the bounded-set operation defined in
    2.10.30, p. 195, for an arbitrary unit
    normal. The construction distinguishes empty sections
    and nonempty sections of zero length. *)
Theorem steiner_symmetrisation_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (hu : B u u= 1) (S : set (inner_metric_space hB)) :
  metric_set_bounded S -> exists T, is_steiner_symmetrisation hB u S T.
Proof.
move=> hb.
pose F y := centered_section (@normal_sections_bounded R V B hB u hu S hb y).
pose T : set V := [set x | F (normal_foot hB u x) (inner_coordinate hB u x)].
exists T; constructor=> // y hy.
have hp t : T (y+t*:u) <-> F y t.
  change (F (normal_foot hB u (y+t*:u)) (inner_coordinate hB u (y+t*:u)) <-> F y t).
  by rewrite (@normal_line_foot R V B hB u hu y t hy)
    (@normal_line_coordinate R V B hB u hu y t hy).
have he : normal_scalar_section u T y=F y.
  apply/seteqP; split=> t; [exact: (hp t).1|exact: (hp t).2].
rewrite he /F; exact: centered_section_specification.
Qed.
