(** Federer (1969), 2.5.7, p. 99: order of the covering-set integral
    coordinates of tau in case p=1. These supporting pairing consequences
    use the already proved integral order and equality laws; the comparison
    of densities is only almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralUniqueness MeasureNonnegativeIntegral MeasureIntegralComparison MeasureIntegralOrderEquality
  SummableRealFunctionUP TotalScalarLpUP TotalScalarPairingValue TotalLpPairingBound LpConjugatePair
  CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_total_pairing_value]: positivity of the integral
    coordinates of tau in Federer 2.5.7, p. 99 *)
Lemma nonnegative_total_pairing_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f u : X -> R) :
  summable_real_functions mu (fun x => (f x*u x)%R) ->
  (forall x, (0 <= f x)%R) -> (forall x, (0 <= u x)%R) ->
  (0 <= total_scalar_pairing mu f u)%R.
Proof.
move=> hs hf hu.
have hi := @total_scalar_pairing_specification R X mu f u hs.
have hp : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand (fun x => (f x*u x)%R))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x*u x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: mulr_ge0 (hf x) (hu x).
have [hi' h0] := @nonnegative_measurable_function_integral R X mu hm _ hi.1 hp.
have he := measure_integral_unique hi' hi.
by rewrite he lee_fin in h0.
Qed.

(** Source for [positive_lp_pairing_almost_order]: monotonicity of the
    integral coordinates in Federer 2.5.7, p. 99 This supporting lemma
    permits any nonnegative conjugate-space test, not only indicators. *)
Lemma positive_lp_pairing_almost_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (f u v : X -> R) :
  is_lp_conjugate_pair p q -> total_scalar_lp mu p f ->
  total_scalar_lp mu q u -> total_scalar_lp mu q v ->
  (forall x, (0 <= f x)%R) ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  (total_scalar_pairing mu f u <= total_scalar_pairing mu f v)%R.
Proof.
move=> hpq hf hu hv hf0 huv.
have hiu := (@total_lp_pairing_specification_and_bound R X mu hm p q f u hpq hf hu).1.
have hiv := (@total_lp_pairing_specification_and_bound R X mu hm p q f v hpq hf hv).1.
have hh : (total_scalar_pairing mu f u)%:E <= (total_scalar_pairing mu f v)%:E.
  apply: (@measure_integral_monotone R X mu hm _ _ _ _ hiu hiv).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huv)=> x hx.
  exists (f x*u x)%:E,(f x*v x)%:E; split; first by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; apply: (ler_wpM2l (hf0 x)); exact: hx.
by rewrite lee_fin in hh.
Qed.

(** Source for [ordered_characteristic_pairing_equality]: equality of a
    covering-set coordinate forces equality almost everywhere on that set,
    proving strictness of tau in Federer 2.5.7, p. 99 Only positivity of the
    characteristic test is used for order. *)
Lemma ordered_characteristic_pairing_equality (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s u v : X -> R) :
  is_characteristic_function A s -> total_scalar_lp mu 1 s ->
  total_scalar_lp mu +oo u -> total_scalar_lp mu +oo v ->
  (forall x, (0 <= s x)%R) ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  total_scalar_pairing mu s u=total_scalar_pairing mu s v ->
  measure_almost_everywhere mu [set x | A x -> u x=v x].
Proof.
move=> hs hsl hu hv hs0 huv he.
have hpq : @is_lp_conjugate_pair R 1 +oo by right; left.
have hiu := (@total_lp_pairing_specification_and_bound R X mu hm 1 +oo s u hpq hsl hu).1.
have hiv := (@total_lp_pairing_specification_and_bound R X mu hm 1 +oo s v hpq hsl hv).1.
rewrite -he in hiv.
have horder : measure_almost_everywhere mu [set x | exists a b : R,
    partial_function_graph (real_total_integrand (fun x => (s x*u x)%R)) x a%:E /\
    partial_function_graph (real_total_integrand (fun x => (s x*v x)%R)) x b%:E /\ (a <= b)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ huv)=> x hx.
  exists (s x*u x)%R,(s x*v x)%R; split; first by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  apply: (ler_wpM2l (hs0 x)); exact: hx.
have heq := @measure_integral_order_equality R X mu hm _ _ _ hiu hiv horder.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ heq)=> x [z [hz hz']] hx.
have hzu := (proj1 (real_total_integrand_graph _ x z)) hz.
have hzv := (proj1 (real_total_integrand_graph _ x z)) hz'.
rewrite (characteristic_on_set hs hx) mul1r in hzu.
rewrite (characteristic_on_set hs hx) mul1r in hzv.
apply: EFin_inj; by rewrite hzu hzv.
Qed.
