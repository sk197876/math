(** Federer (1969), 4.1.19, p. 377: pass from
    compact smooth tests to the class-one weak
    derivative equation. The supporting integral estimate
    uses a comass error only on the original
    compact coefficient carrier. The measure may have
    infinite total mass and the coefficient may vanish. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric
  ContinuousDualUP RealFunctionalNormUP PartialFunctionBasic
  PartialExtendedArithmetic PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAbsolute MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic
  CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_summable_dual_uniform_integral_error]:
    the compact-uniform passage to the original
    class-one relation in Federer 4.1.19,
    p. 377, using the original integral
    inequalities of 2.4.4(7)–(8), pp. 82–83.
    Only the actual coefficient support controls
    the error; neither dual field needs
    a global pointwise bound in this implication. *)
Theorem compact_summable_dual_uniform_integral_error
    (R : realType) (X : topologicalType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDual : is_continuous_dual hN ed DN)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (xi : @CompactSummableField.space R X V N hN mu hm)
    (K : set X) (phi psi : X -> D) (a b error : R) :
  (forall x, ~K x ->
    @compact_summable_field_value R X V N hN mu hm xi x=0) ->
  is_measure_integral mu (real_total_integrand (fun x =>
    ed (phi x) (@compact_summable_field_value R X V N hN mu hm xi x))) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x =>
    ed (psi x) (@compact_summable_field_value R X V N hN mu hm xi x))) b%:E ->
  (forall x, K x -> DN (phi x-psi x) <= error) ->
  `|a-b| <= error*@compact_summable_field_size R X V N hN mu hm xi.
Proof.
move=> hOff hPhi hPsi hError.
pose value := @compact_summable_field_value R X V N hN mu hm xi.
pose size := @compact_summable_field_size R X V N hN mu hm xi.
pose f := fun x => ed (phi x) (value x).
pose g := fun x => ed (psi x) (value x).
have hDifference := @real_total_integral_subtract R X mu hm f g a b hPhi hPsi.
have [c [hAbsolute hLower]] := @measure_integral_absolute_bound R X mu hm
  (real_total_integrand (fun x => f x-g x)) (a-b)%:E hDifference.
have hNorm := @real_total_integral_scale R X mu hm
  (fun x => N (value x)) size error
  (@compact_summable_field_size_integral R X V N hN mu hm xi).
have hPoint (x : X) : `|f x-g x| <= error*N (value x).
  have [hx|hx] := pselect (K x).
  - have hLinear : ed (phi x-psi x) (value x)=f x-g x.
      have h := congr1 (fun ell : Hom V R^o => ell (value x))
        (linB (hom_linear ed) (phi x) (psi x)).
      exact: h.
    rewrite -hLinear.
    have hBound := real_functional_norm_bound
      (continuous_dual_norm_laws hDual (phi x-psi x)) (value x).
    exact: (le_trans hBound (ler_wpM2r
      (real_seminorm_nonnegative hN.1 (value x)) (@hError x hx))).
  - have hFZero : f x=0%R.
      rewrite /f /value (@hOff x hx).
      exact: (lin0 (hom_linear (ed (phi x)))).
    have hGZero : g x=0%R.
      rewrite /g /value (@hOff x hx).
      exact: (lin0 (hom_linear (ed (psi x)))).
    have hNZero : N (value x)=0%R.
      rewrite /value (@hOff x hx); exact: (real_seminorm_zero hN.1).
    by rewrite hFZero hGZero hNZero subrr normr0 mulr0.
have hOrder : measure_almost_everywhere mu
    (partial_extended_le_locus
      (partial_extended_function_absolute_value
        (real_total_integrand (fun x => f x-g x)))
      (real_total_integrand (fun x => error*N (value x)))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  exists (`|f x-g x|)%:E,(error*N (value x))%:E; split.
  - exists (f x-g x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first by apply/real_total_integrand_graph.
    by rewrite lee_fin; exact: hPoint.
have hUpper := @measure_integral_monotone R X mu hm _ _ c
  (error*size)%:E hAbsolute hNorm hOrder.
have hBound := le_trans hLower hUpper.
by rewrite abse_EFin lee_fin in hBound.
Qed.
