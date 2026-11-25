(** Federer (1969), 4.1.19, p. 377: the
    scalar representation of the two coefficient
    fields uses Lebesgue measure on the original
    open U. The preceding item supplies that
    exact open-domain measure and its Radon laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain MeasureUP RadonMeasureUP FunctionLatticeSeminormUP
  FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP LpConjugatePair LpFunctionalDensityUP
  LpFunctionalDensity CurrentDomainRadonSigmaFinite
  EuclideanOpenDomainMeasure RadonBoundedLoneDensity BoundedScalarLoneDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_open_bounded_lone_density]:
    apply 2.5.10, p. 101, on the
    literal original U in Federer 4.1.19,
    p. 377. The same pointwise density
    bound is obtained for every open U,
    including empty U and U of infinite
    measure. No ambient zero extension is used. *)
Theorem euclidean_open_bounded_lone_density (R : realType) n
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (A : (current_domain R n U -> R) -> R) (c : R) :
  0 <= c ->
  is_linear_functional_on_functions
    (total_scalar_lp (@euclidean_open_domain_measure R n U) 1) A ->
  (forall f,
    total_scalar_lp (@euclidean_open_domain_measure R n U) 1 f ->
    `|A f| <= c*finite_total_scalar_lp_norm
      (@euclidean_open_domain_measure R n U) 1 f) ->
  exists k : current_domain R n U -> R,
    is_real_lattice_density (@euclidean_open_domain_measure R n U)
      (total_scalar_lp (@euclidean_open_domain_measure R n U) 1) A k /\
    forall x, `|k x| <= c.
Proof.
have hMeasure := @euclidean_open_domain_measure_laws R n U hU.
exact: (@radon_bounded_lone_density R (current_domain R n U)
  (@euclidean_open_domain_measure R n U) hMeasure.1 hMeasure.2 A c).
Qed.

(** Source for [euclidean_open_bounded_lone_functional_representation]:
    the full scalar duality used for the
    form coefficients in Federer 4.1.19,
    p. 377, holds on the literal
    original open U. The earlier compact exhaustion
    supplies countable measurability internally. The chosen
    density has the original pointwise bound and
    exactly the original L-infinity operator norm. *)
Theorem euclidean_open_bounded_lone_functional_representation
    (R : realType) n (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (A : (current_domain R n U -> R) -> R) (c : R) :
  0 <= c ->
  is_linear_functional_on_functions
    (total_scalar_lp (@euclidean_open_domain_measure R n U) 1) A ->
  (forall f,
    total_scalar_lp (@euclidean_open_domain_measure R n U) 1 f ->
    `|A f| <= c*finite_total_scalar_lp_norm
      (@euclidean_open_domain_measure R n U) 1 f) ->
  exists k : current_domain R n U -> R,
    is_lp_functional_density (@euclidean_open_domain_measure R n U)
      1 +oo A k /\
    (forall x, `|k x| <= c) /\
    total_scalar_lp_norm (@euclidean_open_domain_measure R n U) +oo k =
      function_operator_seminorm
        (total_scalar_lp (@euclidean_open_domain_measure R n U) 1) A
        (finite_total_scalar_lp_norm (@euclidean_open_domain_measure R n U) 1).
Proof.
move=> hC hLinear hBound.
have hMeasure := @euclidean_open_domain_measure_laws R n U hU.
have hCountable := @current_domain_radon_countably_measurable R n U hU
  (@euclidean_open_domain_measure R n U) hMeasure.1 hMeasure.2.
have [k [hK hCap]] := @euclidean_open_bounded_lone_density R n U hU
  A c hC hLinear hBound.
have [hDensity hNorm] := @bounded_scalar_lone_density_full R
  (current_domain R n U) (@euclidean_open_domain_measure R n U) hMeasure.1
  hCountable A k c hC hK hCap.
exists k; split; first exact: hDensity.
split; first exact: hCap.
have hConjugate : is_lp_conjugate_pair (1 : \bar R) +oo.
  by right; left.
exact: (@lp_functional_density_norm R (current_domain R n U)
  (@euclidean_open_domain_measure R n U) hMeasure.1 1 +oo A k
  hConjugate hDensity).
Qed.
