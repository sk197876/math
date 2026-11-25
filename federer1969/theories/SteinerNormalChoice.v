(** Normal-choice independence of the hyperplane operation in Federer
    (1969), 2.10.30, p. 195. Reversing the normal reverses the scalar line
    coordinates without changing centred sections or their lengths. The
    unit-normal uniqueness theorem then identifies the results for any two
    unit normals defining the same hyperplane. Source context:
    UnitNormalUniqueness.v and CenteredSectionReflection.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric OrthonormalFamilies Bilinear
  RealMetricBackground CoveringFamilyUP UnitNormalGeometry UnitNormalUniqueness
  SteinerSymmetrisationUP SteinerSymmetrisationLaws SteinerSymmetrisation
  CenteredSectionReflection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_scalar_section_reverse]: supporting
    scalar change of coordinate t mapped to -t
    when reversing the perpendicular direction in
    2.10.30, p. 195. *)
Lemma normal_scalar_section_reverse (R : realType) (V : lmodType R)
    (u y : V) (A : set V) :
  normal_scalar_section (-u) A y=(fun t : real_line_metric R=> -t) @^-1` normal_scalar_section u A y.
Proof.
apply/seteqP; split=> t;
  change (A (y+t*:(-u))->A (y+(-t)*:u)) ||
  change (A (y+(-t)*:u)->A (y+t*:(-u)));
  by rewrite scalerN scaleNr.
Qed.

(** Source for [normal_coordinate_negated_normal]: supporting
    sign change of the scalar normal functional
    for normal-choice independence in 2.10.30,
    p. 195. *)
Lemma normal_coordinate_negated_normal (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u x : V) :
  inner_coordinate hB (-u) x= -inner_coordinate hB u x.
Proof.
rewrite !inner_coordinateE -[ -u]scaleN1r (bilZr (inner_bilinear hB)).
change ((-1)*B x u= -B x u); exact: mulN1r.
Qed.

(** Source for [steiner_reverse_normal]: supporting
    invariance of the defining normal-line laws
    in 2.10.30, p. 195, under u mapped
    to -u. Empty and null sections are retained. *)
Theorem steiner_reverse_normal (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u : V) (S T : set V) :
  is_steiner_symmetrisation hB u S T -> is_steiner_symmetrisation hB (-u) S T.
Proof.
move=> hT; have hu := steiner_unit_normal_law hT; constructor.
- by rewrite -(inner_norm_sqr hB (-u)) inner_normN (unit_normal_norm hB hu) expr1n.
- move=> y hy.
  have hyu : inner_coordinate hB u y=0.
    apply: oppr_inj; by rewrite oppr0 -normal_coordinate_negated_normal hy.
  rewrite !normal_scalar_section_reverse.
  exact (centered_section_reverse_coordinates (steiner_normal_sections_law hT hyu)).
Qed.

(** Source for [steiner_hyperplane_unique]: supporting
    well-definedness with respect to the n-1
    dimensional hyperplane, rather than an oriented
    normal, in 2.10.30, p. 195. *)
Theorem steiner_hyperplane_unique (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (H : set V)
    (u v : V) (S T U : set V) :
  @is_unit_normal R V B hB H u -> @is_unit_normal R V B hB H v ->
  is_steiner_symmetrisation hB u S T -> is_steiner_symmetrisation hB v S U -> T=U.
Proof.
move=> hU hV hT hU0.
case: (unit_normal_same_hyperplane hU hV)=> he.
- move: hU0; rewrite he=> hU0; exact (steiner_symmetrisation_unique hT hU0).
- move: hU0; rewrite he=> hU0; exact (steiner_symmetrisation_unique (steiner_reverse_normal hT) hU0).
Qed.

(** Source for [steiner_symmetrisation_hyperplane_independent]: supporting
    independence of all boundedness and normal
    choices in the operation of 2.10.30,
    p. 195. Only the hyperplane and source
    set determine the opaque resulting set. *)
Theorem steiner_symmetrisation_hyperplane_independent (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (H : set V) (u v : V)
    (hU : @is_unit_normal R V B hB H u) (hV : @is_unit_normal R V B hB H v)
    (S : set (inner_metric_space hB)) (hb hc : metric_set_bounded S) :
  steiner_symmetrisation hB hU.1 hb=steiner_symmetrisation hB hV.1 hc.
Proof.
exact (steiner_hyperplane_unique hU hV (steiner_symmetrisation_specification hB hU.1 hb)
  (steiner_symmetrisation_specification hB hV.1 hc)).
Qed.
