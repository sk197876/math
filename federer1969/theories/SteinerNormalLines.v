(** Ambient normal-line laws of Steiner symmetrisation in Federer (1969),
    2.10.30, p. 195. Express the scalar specification as the printed
    intersections with actual affine lines, and identify the ambient
    Hausdorff lengths using the already proved line isometries. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies RealMetricBackground
  SteinerSymmetrisationUP CenteredSectionUP CenteredSectionLaws UnitNormalGeometry NormalLineLength
  HausdorffLength LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_affine_line]: direct straight line
    perpendicular to the hyperplane in 2.10.30,
    p. 195, parametrised by its normal direction.
    The subsequent statements require a unit normal
    and a foot in the orthogonal hyperplane. *)
Definition normal_affine_line (R : realType) (V : lmodType R) (u y : V) : set V :=
  (fun t : R=>y+t*:u) @` setT.

(** Source for [normal_affine_line_intersection]: supporting identity
    between ambient intersection and scalar section image in 2.10.30, p. 195 *)
Lemma normal_affine_line_intersection (R : realType) (V : lmodType R)
    (u y : V) (S : set V) :
  normal_affine_line u y `&` S=(fun t : R=>y+t*:u) @` normal_scalar_section u S y.
Proof.
apply/seteqP; split=> x.
- move=> [[t _ <-] ht]; by exists t.
- move=> [t ht <-]; split=> //; by exists t.
Qed.

(** Source for [steiner_normal_line_length]: direct
    H^1(L intersect T)=H^1(L intersect S)
    in 2.10.30, p. 195. This uses the
    actual ambient Hausdorff length, not only
    the scalar-section surrogate. *)
Theorem steiner_normal_line_length (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u y : V)
    (S T : set (inner_metric_space hB)) :
  is_steiner_symmetrisation hB u S T -> inner_coordinate hB u y=0 ->
  @hausdorff_length R (inner_metric_space hB) (normal_affine_line u y `&` T)=
    @hausdorff_length R (inner_metric_space hB) (normal_affine_line u y `&` S).
Proof.
move=> hT hy; have hu := steiner_unit_normal_law hT.
rewrite !normal_affine_line_intersection
  !(@normal_line_hausdorff_length R V B hB u y hu hy).
exact (centered_section_length_law (steiner_normal_sections_law hT hy)).
Qed.

(** Source for [steiner_normal_line_alternatives]: direct
    two alternatives defining T on each perpendicular
    line in 2.10.30, p. 195. A closed
    centred segment is represented by the image
    of [-r,r]; radius zero is a point and
    remains distinct from an empty line section. *)
Theorem steiner_normal_line_alternatives (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u y : V)
    (S T : set (inner_metric_space hB)) :
  is_steiner_symmetrisation hB u S T -> inner_coordinate hB u y=0 ->
  (normal_affine_line u y `&` S=set0 /\ normal_affine_line u y `&` T=set0) \/
  exists r : R, 0<=r /\ normal_affine_line u y `&` S !=set0 /\
    normal_affine_line u y `&` T=(fun t : R=>y+t*:u) @` `[-r,r] /\
    @hausdorff_length R (inner_metric_space hB) (normal_affine_line u y `&` T)=
      @hausdorff_length R (inner_metric_space hB) (normal_affine_line u y `&` S).
Proof.
move=> hT hy; have hs := steiner_normal_sections_law hT hy.
case: (pselect (normal_scalar_section u S y !=set0))=> [hne|hne].
- have [r [hr hBr]] := centered_section_shape_law hs ((centered_section_support_law hs).1 hne).
  right; exists r; split=> //; split.
  + rewrite normal_affine_line_intersection; exact: image_nonempty hne.
  split.
  + by rewrite normal_affine_line_intersection hBr.
  + exact: steiner_normal_line_length hT hy.
- have hA : normal_scalar_section u S y=set0.
    apply/seteqP; split=> t; last by case.
    by move=> ht; exfalso; apply: hne; exists t.
  have hB0 := (centered_section_empty hs).1 hA.
  left; by rewrite !normal_affine_line_intersection hA hB0 !image_set0.
Qed.
