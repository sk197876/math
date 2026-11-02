(** Federer (1969), 2.2.15, p. 71, necessity in the final target
    characterisation. Test the universal assertion on Borel maps from R,
    using sealed finite interpolation and the finite-sample closure property
    of Baire maps. The target is explicitly nonempty; see
    BaireEmptyTargetBoundary.v. Separability is unnecessary for this
    implication. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground BorelFunctionUP BaireFunctions
  FiniteCurveApproximationUP FiniteBorelInterpolationUP FiniteBorelInterpolationSealed
  BaireCurveSamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_baire_target_necessary]: direct necessity
    in Federer 2.2.15, p. 71, with the explicit
    nonempty-target boundary clarification. It suffices to test
    real-domain Borel maps; every prescribed finite set of target
    values is then approximable by one continuous curve. *)
Theorem borel_baire_target_necessary (R : realType) (Y : metricType R) (y0 : Y) :
  (forall f : real_line_metric R -> Y, is_borel_function f -> is_baire_function f) ->
  has_finite_curve_approximation Y.
Proof.
move=> h Z hZ e he.
pose w := @FiniteBorelInterpolation.value R Y Z y0 hZ.
have hw := @FiniteBorelInterpolation.laws R Y Z y0 hZ.
have hb : is_baire_function w.1 := h w.1 (finite_interpolation_borel hw).
have [c [hc happ]] := @baire_real_domain_curve_samples R Y w.1 hb
  w.2 (finite_interpolation_inputs hw) e he.
exists c; split=> // z hz.
have [x hx heq] := finite_interpolation_covers hw hz.
rewrite -heq; exact: happ x hx.
Qed.
