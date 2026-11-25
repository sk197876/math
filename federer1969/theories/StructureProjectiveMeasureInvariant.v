(** Federer (1969), 3.3.4, pp. 290–291: the
    actual reference Hausdorff measure on T(U) is
    invariant and has centre-independent ball masses.
    The original inherited metric and all test
    subsets occur in the image-measure identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  StructureProjectiveSpace StructureProjectiveMeasure StructureProjectiveActionTopology
  StructureProjectiveActionLaws HomogeneousBallMass HausdorffMeasure HausdorffIsometryMeasurability
  EuclideanOrthogonalInvariantMeasures IsotropyGroupTopology LinearGroupTopology LinearGroupSealed
  MeasurePushforward MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Invariance.
Variable R:realType.
Variable m:nat.
Local Notation hB:=(@euclidean_inner_productP R m.+1).
Local Notation hb:=(@coordinate_basisP R m.+1).
Local Notation O:=(euclidean_orthogonal_group R m.+1).
Local Notation M:=(structure_projective_space R m).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction (linear_group_mul hB hb)
  (linear_group_inv hB hb) (linear_group_unit hB hb) O mulS invS eS.

(** Source for [structure_projective_measure_invariant]:
    H^m on T(U) is invariant under its actual
    orthogonal action, Federer 3.3.4, p. 290.
    Both actual inverse laws and the isometric
    metric identity discharge the image-measure theorem. *)
Theorem structure_projective_measure_invariant (g:O):
  measure_pushforward (structure_projective_action g) (@structure_projective_measure R m)=
    @structure_projective_measure R m.
Proof.
have [hLeft hRight]:=structure_projective_action_cancel hS g.
exact:(@hausdorff_bijective_isometry_pushforward R M M
  (structure_projective_action g) (structure_projective_action (invS g))
  hLeft hRight (@structure_projective_action_isometry R m g) m).
Qed.

(** Source for [structure_projective_closed_ball_mass]:
    the closed-ball numerator in the density ratios
    of Federer 3.3.4, p. 291, is independent
    of the centre z in the actual T(U). *)
Theorem structure_projective_closed_ball_mass (x y:M) (r:R):
  structure_projective_measure (metric_closed_ball x r)=
    structure_projective_measure (metric_closed_ball y r).
Proof.
exact:(@transitive_invariant_closed_ball_mass R M (set_type O)
  (@structure_projective_action R m) (@structure_projective_measure R m)
  (@structure_projective_action_isometry R m)
  (@structure_projective_action_transitive R m)
  structure_projective_measure_invariant x y r).
Qed.

(** Source for [structure_projective_open_ball_mass]:
    open-ball masses in the actual I_j inverse-image
    formula of Federer 3.3.4, pp. 291–292,
    also do not depend on the projective centre. *)
Theorem structure_projective_open_ball_mass (x y:M) (r:R):
  structure_projective_measure [set z|mdist x z<r]=
    structure_projective_measure [set z|mdist y z<r].
Proof.
exact:(@transitive_invariant_open_ball_mass R M (set_type O)
  (@structure_projective_action R m) (@structure_projective_measure R m)
  (@structure_projective_action_isometry R m)
  (@structure_projective_action_transitive R m)
  structure_projective_measure_invariant x y r).
Qed.
End Invariance.
