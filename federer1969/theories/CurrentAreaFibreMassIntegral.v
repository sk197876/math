(** Federer (1969), 4.1.25, p. 383: the
    scalar mass sum over the full fibre is summable
    on the target. Reuse the original weighted area
    formula, 3.2.3(2), p. 243, and its bounded
    Jacobian comparison. No finite-total-measure hypothesis
    on the source is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric EuclideanLebesgueDimensions ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralPartsExist
  MeasureUpperIntegralPositivePart NonnegativeExtendedNormOrder LipschitzUP HausdorffMeasure
  EuclideanJacobianMeasurable EuclideanJacobianUpperBound
  JacobianDensityMeasure BoundedDensityIntegralComparison
  AreaNonnegativeWeighted FibreNonnegativeSum NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section FibreMassIntegral.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable r : R_n R m -> R.
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation S := (fun y => fibre_nonnegative_sum f (fun x => (r x)%:E) y).

(** Source for [current_area_fibre_mass_integral]: the
    finite mass estimate for the fibre sum in
    Federer 4.1.25, p. 383. The original full fibre
    is retained, and the estimate is the m-th power
    of the supplied actual Lipschitz bound. *)
Theorem current_area_fibre_mass_integral (L a : R) :
  (0 < L)%R -> is_metric_lipschitz_bound setT f L ->
  (forall x, (0 <= r x)%R) ->
  is_measure_integral mu
    (partial_function_total (fun x => ((r x)%:E : extended_real_line R))) a%:E ->
  exists b : R, is_measure_integral H
    (partial_function_total (fun y => (S y : extended_real_line R))) b%:E /\
    (0 <= b <= L^+m*a)%R.
Proof.
move=> hL hLip hNonnegative hIntegral.
have hGlobal : is_metric_lipschitz setT f by exists L.
have hMu := euclidean_lebesgue_is_measure R m.
have hNu := euclidean_jacobian_measure_is_measure hGlobal.
have hPositive x : 0 <= (r x)%:E by rewrite lee_fin; exact: hNonnegative.
have [b [hSource hTarget]] := @area_nonnegative_weighted_integral R m n f
  (fun x => ((r x)%:E : extended_real_line R)) hGlobal hIntegral.1 hPositive.
have hBNonnegative : 0 <= b :=
  nonnegative_total_integral_value_ge0 hNu hPositive hSource.
have hPower : (0 < L^+m)%R := exprn_gt0 m hL.
have hBound : b <= (L^+m)%:E * a%:E.
  exact: (@bounded_density_integral_comparison R X mu
    (euclidean_jacobian_measure f) hMu (extended_euclidean_jacobian f)
    (fun x => ((r x)%:E : extended_real_line R)) (L^+m)%R a%:E b
    (euclidean_jacobian_measure_laws f)
    (extended_euclidean_jacobian_measurable hGlobal)
    (euclidean_jacobian_nonnegative_almost hGlobal) hPower
    (euclidean_jacobian_global_upper_bound (ltW hL) hLip)
    hPositive hIntegral hSource).
have hFinite : b \is a fin_num.
  rewrite (ge0_fin_numE hBNonnegative).
  apply: le_lt_trans hBound _; by rewrite -EFinM ltry.
exists (fine b); rewrite fineK //; split; first exact: hTarget.
apply/andP; split.
- move: hBNonnegative; by rewrite -(fineK hFinite) lee_fin.
- move: hBound; by rewrite -(fineK hFinite) -EFinM lee_fin.
Qed.

(** Source for [current_area_fibre_mass_almost_finite]:
    almost-everywhere absolute convergence needed for the
    vector formula in Federer 4.1.25, p. 383,
    from the preceding weighted area estimate and
    2.4.3(4), p. 82. The indexing fibre may be
    infinite or uncountable. *)
Theorem current_area_fibre_mass_almost_finite :
  is_metric_lipschitz setT f ->
  (forall x, (0 <= r x)%R) ->
  (exists a : R, is_measure_integral mu
    (partial_function_total (fun x => ((r x)%:E : extended_real_line R))) a%:E) ->
  measure_almost_everywhere H [set y | S y < +oo].
Proof.
move=> [L [hL hLip]] hNonnegative [a hIntegral].
have [b [hTarget _]] := current_area_fibre_mass_integral hL hLip hNonnegative hIntegral.
have hH := @hausdorff_measure_is_measure R Y m.
have hUpper : measure_upper_integral H
    (partial_function_total (fun y => (S y : extended_real_line R))) < +oo.
  rewrite (measure_upper_integral_unique
    (measure_upper_integral_specification H _) hTarget.2.1).
  exact: ltry.
have hAlmost := (@measure_finite_upper_integral_consequences R Y H hH
  (partial_function_total (fun y => (S y : extended_real_line R))) hUpper).2.
apply: (measure_almost_everywhere_mono hH _ hAlmost) => y [v [hValue hFinite]].
change (S y < +oo).
move: hFinite; by rewrite -(hValue : S y = v).
Qed.
End FibreMassIntegral.
