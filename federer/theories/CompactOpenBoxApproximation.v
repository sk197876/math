(** Federer (1969), 3.2.41, printed p. 278, first proof
    sentence: approximate the original compact sets by finite
    disjoint open-box unions inside arbitrarily small tubes,
    retaining at least the original actual Lebesgue volume. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EqualCoordinateCubeGridUP CompactEqualCubeGrid
  FiniteMeetingCubeCover ClosedCubeCoverOpenBoxes FiniteDisjointOpenBoxFamilyUP
  MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_open_box_approximation_exists]: supporting
    actual compact approximation in Federer 3.2.41, p. 278.
    An arbitrarily fine finite closed grid covers K, including
    its boundary points. Retain precisely the cells meeting K;
    their proved null boundary remainders justify replacing them
    by genuinely disjoint proper open boxes. No approximation,
    null-face, mass or near-source law is an extra premise. *)
Theorem compact_open_box_approximation_exists (R:realType) n
    (K:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  compact K ->K !=set0 ->0<r ->
  exists (I:finType) (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))),
    is_finite_disjoint_open_box_family a b G /\(\bigcup_i G i) !=set0 /\
    (@euclidean_lebesgue_measure R n K<=@euclidean_lebesgue_measure R n (\bigcup_i G i))%E /\
    (\bigcup_i G i) `<=` metric_open_thickening K r.
Proof.
move=> hK hKNe hr.
pose h:R:=r/n.+1%:R.
have hDen:(0<(n.+1%:R:R)) by rewrite ltr0n.
have hDen0:(n.+1%:R:R)!=0 by rewrite gt_eqF.
have hh:0<h by rewrite /h divr_gt0.
have hCancel:h*n.+1%:R=r by rewrite /h divfK.
have hSuccessor:(n.+1%:R:R)=n%:R+1 by rewrite -addn1 natrD.
have hRelation:n%:R*h+h=r.
  by move:hCancel; rewrite hSuccessor mulrDr mulr1 [h*n%:R]mulrC.
have hMesh:n%:R*h<r by lra.
have [k [corner [P [hP hCover]]]]:=@compact_equal_cube_grid_encloses R n K h hK hh.
have [I [a [Q [hQ hMeet hSource hNull]]]]:=
  @finite_meeting_coordinate_grid_cover R n k corner h P K hP hCover.
have [b [G [hFamily [hGNe [hMass hNear]]]]]:=
  @closed_cube_cover_open_boxes R n I a h r Q K hh hQ hMeet hSource hNull hMesh hKNe.
exists I,a,b,G; split; first exact hFamily.
split; first exact hGNe.
by split.
Qed.
