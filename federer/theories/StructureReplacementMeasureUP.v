(** Federer (1969), 3.3.16, pp. 299–300: independent
    mathematical laws shared by the four replacement measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions HausdorffMeasure RectifiableSetUP MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_structure_replacement_measure]: independent
    covering/comparison laws used in Federer 3.3.16, p. 299,
    via 2.10.6, 2.10.8 and 2.10.10. Require an ordinary Borel
    regular measure, a positive finite uniform projection bound,
    and agreement on the original bounded Lipschitz images of
    3.2.26. No structure, decomposition, pure-set, integral-geometric
    nullity or rectifiability conclusion is a field. Actual spherical,
    exterior-diameter, convex integral-geometric and Gross instances
    are proved separately from their sealed public laws. *)
Record is_structure_replacement_measure (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):Prop:={
  (** Source for [structure_replacement_measure_law]: ordinary
      measure requirement in Federer 3.3.16, p. 299. *)
  structure_replacement_measure_law:is_measure phi;
  (** Source for [structure_replacement_borel_regular]: Borel
      regularity used to retain arbitrary sources in 3.3.16, p. 299. *)
  structure_replacement_borel_regular:is_borel_regular_measure phi;
  (** Source for [structure_replacement_projection_bound]: supporting
      uniform projection comparison from 2.10.6, p. 173, used in
      Federer 3.3.16, p. 299. Every original subset is retained. *)
  structure_replacement_projection_bound:exists c:R,(0<c)%R /\
    forall A (p:euclidean_projection_space R n m),
      euclidean_lebesgue_measure m (euclidean_projection_linear p @` A)<=c%:E*phi A;
  (** Source for [structure_replacement_rectifiable_agreement]:
      original bounded-image agreement of 3.2.26, p. 261, used
      in Federer 3.3.16, p. 299. It does not assert agreement
      on arbitrary original countably measure rectifiable sets. *)
  structure_replacement_rectifiable_agreement:forall A,
    is_m_rectifiable m A ->phi A=@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m A
}.
