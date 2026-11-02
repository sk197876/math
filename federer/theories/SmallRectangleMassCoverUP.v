(** Abstract single-scale measure covers supporting Federer
    (1969), 2.8.20, p. 152. Saks1934 Lemma B,
    pp. 258–259, constructs small-integral functions with
    large averages on small rectangles. We use the associated
    measures and allow a null exceptional set. Removing all
    such exceptions over countably many scales retains a target
    of area one. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ScalarPlaneRectangles ScalarMetricPlane MeasureUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_unit_square]: fixed positive-area
    target used in the local proof of Federer 2.8.20,
    p. 152. It suffices to obstruct a Vitali
    selection on this square after removing null exceptions. *)
Definition scalar_unit_square (R : realType) : set (scalar_metric_plane R) :=
  scalar_closed_rectangle (0 : R)%R 1 0 1.

(** Source for [scalar_unit_square_area]: supporting unit
    area of the target for the counterexample in Federer
    2.8.20, p. 152, from the rectangle volume formula. *)
Lemma scalar_unit_square_area (R : realType) :
  scalar_plane_lebesgue (@scalar_unit_square R) = 1.
Proof. by rewrite /scalar_unit_square scalar_closed_rectangle_value ?ler01 // !subr0 mulr1. Qed.

(** Source for [is_small_rectangle_mass_cover]: abstract
    single-scale large-average covering measure supporting Federer
    2.8.20, p. 152. Its small budget and small
    rectangles are independent parameters; the exceptional remainder
    is null. This is a supporting strengthening of the measure
    form of Saks1934 Lemma B, pp. 258–259. *)
Record is_small_rectangle_mass_cover (R : realType) (cap budget : R)
    (nu : set (scalar_metric_plane R) -> \bar R)
    (C : set (set (scalar_metric_plane R))) : Prop := {
  (** Source for [small_rectangle_cover_measure]: measure law
      supporting Federer 2.8.20, p. 152. *)
  small_rectangle_cover_measure : is_measure nu;
  (** Source for [small_rectangle_cover_measurable]: measurable
      eligible cells for Federer 2.8.20, p. 152. *)
  small_rectangle_cover_measurable : forall S,
    measure_measurable (@scalar_plane_lebesgue R) S -> measure_measurable nu S;
  (** Source for [small_rectangle_cover_countable]: countably
      many eligible cells in the supporting construction for
      Federer 2.8.20, p. 152. *)
  small_rectangle_cover_countable : countable C;
  (** Source for [small_rectangle_cover_rectangles]: the compact
      nondegenerate eligible rectangles of Federer 2.8.20, p. 152. *)
  small_rectangle_cover_rectangles : forall S, C S -> is_nondegenerate_scalar_rectangle S;
  (** Source for [small_rectangle_cover_diameter]: supporting
      small cell diameters for Federer 2.8.20, p. 152;
      Saks1934 Lemma B (3), p. 258. *)
  small_rectangle_cover_diameter : forall S, C S -> extended_metric_diameter S<=cap%:E;
  (** Source for [small_rectangle_cover_mass]: each eligible
      cell carries at least twice its area, supporting Federer
      2.8.20, p. 152. Any fixed factor exceeding
      the eventual total mass would suffice. *)
  small_rectangle_cover_mass : forall S, C S -> 2 * scalar_plane_lebesgue S<=nu S;
  (** Source for [small_rectangle_cover_remainder]: almost
      coverage of the fixed unit-square target supporting
      Federer 2.8.20, p. 152. *)
  small_rectangle_cover_remainder : scalar_plane_lebesgue
    (@scalar_unit_square R `\` \bigcup_(S in C) S) = 0;
  (** Source for [small_rectangle_cover_cost]: small total
      mass of the single-scale measure, supporting Federer
      2.8.20, p. 152; Saks1934 Lemma B (7), p. 258. *)
  small_rectangle_cover_cost : nu setT<=budget%:E
}.
