(** Federer (1969), 3.2.35, pp. 271--272:
    the explicit empty-product base of the
    dimension induction for the printed formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricSetDistanceUP MetricSetDistanceBasic EuclideanLebesgueDimensions PointMassMeasure
  SteinerTubePolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_tube_zero_dimension]: supporting
    dimension induction for Steiner's formula,
    Federer 3.2.35, pp. 271--272. The
    explicit n=0 extension has one source
    point, zero actual distance and unit tube
    volume at every positive radius. The
    polynomial's single actual coefficient is
    independently proved one. Convexity, boundedness
    or measurability are unnecessary in this base. *)
Lemma steiner_tube_zero_dimension (R:realType)
    (S:set (inner_metric_space (@euclidean_inner_productP R 0))) d:
  S!=set0 ->is_metric_set_distance S d ->is_steiner_tube_volume S d.
Proof.
move=>hNonempty hD r hr.
have [a ha]:=hNonempty.
have hMember x:S x.
  have hEqual:x=a by rewrite (coordinate_zero x) (coordinate_zero a).
  by rewrite hEqual.
have hDistance x:d x=0:=metric_set_distance_member hD (hMember x).
have hTube:[set x|d x<r]=setT.
  apply/seteqP; split=>x hx; first exact Logic.I.
  change (is_true (d x<r)); by rewrite hDistance.
rewrite hTube (@steiner_tube_polynomial_zero_dimension R S r hNonempty) /euclidean_lebesgue_measure.
exact:(@point_mass_in R [the choiceType of inner_metric_space (@euclidean_inner_productP R 0)] 0 setT I).
Qed.
