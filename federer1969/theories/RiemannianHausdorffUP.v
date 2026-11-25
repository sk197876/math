(** Federer (1969), 3.2.46, p. 281: independent
    Hausdorff covering laws for the ORIGINAL path distance.
    All sufficiently small positive cutoffs determine the
    same limiting measure; real degrees and the actual
    Gamma coefficient are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier RiemannianDiameter
  MetricRealPowerCost RealHausdorffNormalisation HausdorffLengthUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_riemannian_hausdorff_scale]: the infimum
    of countable-cover costs using actual rho diameters, as
    required by 3.2.46, p. 281, and 2.10.1–2, pp. 170–171.
    Empty generators are excluded, including degree zero. *)
Record is_riemannian_hausdorff_scale (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (c p delta : R)
    (nu : set (riemannian_metric_space hg) -> \bar R) : Prop := {
  (** Source for [riemannian_hausdorff_scale_lower]: each
      original-rho covering bounds the infimum, supporting
      3.2.46, p. 281. *)
  riemannian_hausdorff_scale_lower : forall B G, countable G ->
    (forall j : @nonempty_metric_sets R [the metricType R of riemannian_metric_space hg],
      G j -> riemannian_diameter hg (val j) <= delta%:E) ->
    B `<=` \bigcup_(j in G) val j ->
    nu B <= nonnegative_sum G (fun j=>metric_real_power_cost c p
      (riemannian_diameter hg (val j)));
  (** Source for [riemannian_hausdorff_scale_greatest]:
      greatest-lower-bound clause of the covering infimum,
      supporting 3.2.46, p. 281. *)
  riemannian_hausdorff_scale_greatest : forall B b,
    (forall G, countable G ->
      (forall j : @nonempty_metric_sets R [the metricType R of riemannian_metric_space hg],
        G j -> riemannian_diameter hg (val j) <= delta%:E) ->
      B `<=` \bigcup_(j in G) val j ->
      b <= nonnegative_sum G (fun j=>metric_real_power_cost c p
        (riemannian_diameter hg (val j)))) -> b <= nu B
}.
Arguments is_riemannian_hausdorff_scale {R n A g} hg c p delta nu.

(** Source for [is_riemannian_hausdorff_measure]: Hausdorff
    measure from the original curve metric, 3.2.46, p. 281.
    The supremum is specified by every cutoff 0<delta<1;
    compatibility with all positive cutoffs is proved separately.
    No metric comparison, volume or Jacobian formula is a law. *)
Record is_riemannian_hausdorff_measure (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R)
    (hp : (0<=p)%R) (mu : set (riemannian_metric_space hg) -> \bar R) : Prop := {
  (** Source for [riemannian_hausdorff_limit_upper]: every
      small-scale infimum is below the final measure,
      supporting 3.2.46, p. 281. *)
  riemannian_hausdorff_limit_upper : forall B delta nu,
    (0<delta<1)%R ->
    is_riemannian_hausdorff_scale hg (real_hausdorff_normalisation hp) p delta nu ->
    nu B <= mu B;
  (** Source for [riemannian_hausdorff_limit_least]: the final
      measure is the least upper bound of small-scale infima,
      supporting 3.2.46, p. 281. *)
  riemannian_hausdorff_limit_least : forall B b,
    (forall delta nu, (0<delta<1)%R ->
      is_riemannian_hausdorff_scale hg (real_hausdorff_normalisation hp) p delta nu ->
      nu B <= b) -> mu B <= b
}.
Arguments is_riemannian_hausdorff_measure {R n A g} hg p hp mu.
