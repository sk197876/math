(** Independent normalized-profile laws supporting the expanded
    continuity argument of Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric ProjectedVolumeMeasurability OrthogonalProjectionProbability
  PartialFunctionBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_normalized_convex_projection_profile]: independent
    helper laws for the corrected exponent-continuity proof of
    Federer 3.2.45, p. 279. The profile records actual projection
    volumes divided by a positive finite source supremum. Positivity,
    the unit bound, attainment, a uniform modulus, and measurability
    are obligations of existence, not premises on the source. *)
Record is_normalized_convex_projection_profile (R : realType) n m (hMN : (m <= n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (c : R)
    (f : orthogonal_projection_metric_space R n m ->
      real_norm_metric_space (scalar_absolute_value_norm R)) : Prop := {
  (** Source for [normalized_projection_profile_value]: supporting
      exact original-volume normalization in Federer 3.2.45, p. 279. *)
  normalized_projection_profile_value : forall p,
    projected_volume_function K p = (c * f p)%:E;
  (** Source for [normalized_projection_profile_nonnegative]: supporting
      nonnegative projected volumes in Federer 3.2.45, p. 279. *)
  normalized_projection_profile_nonnegative : forall p, 0 <= f p;
  (** Source for [normalized_projection_profile_unit_bound]: supporting
      normalization by the original supremum, Federer 3.2.45, p. 279. *)
  normalized_projection_profile_unit_bound : forall p, f p <= 1;
  (** Source for [normalized_projection_profile_attained_one]: supporting
      the actual compact projection maximum in Federer 3.2.45, p. 279. *)
  normalized_projection_profile_attained_one : exists p, f p = 1;
  (** Source for [normalized_projection_profile_relative_modulus]: an
      expanded helper for Federer 3.2.45, p. 279. It uses the original
      projection metric and a constant depending only on the degree. *)
  normalized_projection_profile_relative_modulus : forall p q,
    `|f p-f q| <= m%:R * mdist p q;
  (** Source for [normalized_projection_profile_measurable]: supporting
      the application of 2.4.17, p. 90, in Federer 3.2.45, p. 279. *)
  normalized_projection_profile_measurable : is_measure_measurable_function
    (@orthogonal_projection_probability R n m hMN) (partial_function_total f)
}.
