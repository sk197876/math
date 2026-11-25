(** Federer (1969), 2.10.41, printed p. 200: compact-source part of Jung's
    theorem. Apply 2.10.40 to unit-radius parameters and use its proved
    contact-convex-hull conclusion for the sharp estimate. the finite hull
    background is recorded in ConvexHullFiniteSupport.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  WeightedBallMinimumUP WeightedBallMinimum WeightedBallMinimumGeometry WeightedBallContactNonempty
  EuclideanUnitRadiusParameters EuclideanMinimumBallUP EuclideanMinimumBallLaws
  JungConstant JungContactBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_jung_minimum_ball]: direct compact
    reduction and sharp bound in 2.10.41, p. 200.
    A nonnegative pairwise distance upper bound d
    suffices; equality with the actual diameter is
    unnecessary here. Dimension zero and d=0 are included. *)
Theorem compact_jung_minimum_ball (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (d : R) :
  compact S -> S !=set0 -> 0<=d ->
  (forall a a', S a -> S a' -> inner_norm (@euclidean_inner_productP R n) (a-a')<=d) ->
  exists b r, is_minimum_enclosing_ball S b r /\ r+r<=@jung_factor R n*d.
Proof.
move=> hS hne hd hdiam.
pose P := unit_radius_parameters S.
have hP : compact P := unit_radius_parameters_compact hS.
have hPne : P !=set0 := unit_radius_parameters_nonempty hne.
have hpos : positive_ball_parameter_family P := @unit_radius_parameters_positive R n S.
pose D := @compact_weighted_ball_minimum R n P hP hPne hpos.
have hD := @compact_weighted_ball_minimum_specification R n P hP hPne hpos.
pose b := weighted_minimum_centre D.
pose r := weighted_minimum_scale D.
pose A := weighted_ball_contact_centres P b r.
have hAne : A !=set0 := @weighted_ball_minimum_contacts_nonempty R n P D hP hPne hpos hD.
have hAhull := @weighted_ball_minimum_contact_hull R n P D hP hPne hpos hD.
have hA a : A a -> S a /\ inner_norm (@euclidean_inner_productP R n) (a-b)=r.
  move=> ha.
  have hh : S a /\ inner_norm (@euclidean_inner_productP R n) (b-a)=r.
    by move: ha; rewrite /A /P unit_radius_contact_centres.
  split; first exact hh.1.
  by rewrite -[a-b]opprB inner_normN; exact hh.2.
have hbound : r+r<=@jung_factor R n*d.
  apply: (@inner_hull_sphere_jung_bound R (R_n R n) _ (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) A b r d (@coordinate_basisP R n) hAne hAhull
    (weighted_minimum_scale_nonnegative_law hD) hd).
  - move=> a ha; exact: (hA a ha).2.
  - move=> a a' ha ha'; exact: hdiam a a' (hA a ha).1 (hA a' ha').1.
exists b,r; split=> //; exact: unit_radius_minimum_ball_laws hD.
Qed.
