(** Federer (1969), 2.5.10, p. 101: testing a representing density on
    finite-measure portions of horizontal and vertical segments. This module
    spells out the characteristic-function integral comparisons implicit in
    the geometric argument, using 2.4.4(5), p. 82, and 2.4.5, p. 83. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralComparison MeasureCharacteristicIntegral
  CharacteristicFunctionUP SummableRealFunctionUP SummableRealArithmetic TotalLoneSummability
  TotalScalarLpUP RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_characteristic_total_lone]: the
    characteristic tests on finite H^1 measure sets
    in Federer 2.5.10, p. 101, belong to
    the full summable domain by 2.4.5, p. 83. *)
Lemma finite_characteristic_total_lone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : set X) (s : X -> R) :
  is_characteristic_function E s -> measure_measurable mu E -> mu E < +oo ->
  total_scalar_lp mu 1 s.
Proof.
move=> hs hE hf; apply: (@summable_real_total_lone R X mu hm).
have hfin : mu E \is a fin_num by rewrite ge0_fin_numE ?hf //; exact (@measure_nonnegative R X mu hm E).
exists (fine (mu E)); rewrite fineK //.
exact (@measure_characteristic_integral R X mu hm E s hs hE).
Qed.

(** Source for [representing_density_set_upper_bound]:
    supporting upper test for the horizontal part of
    Federer 2.5.10, p. 101. If k<=c on
    E, its characteristic pairing is at most c*mu(E).
    Finite mu(E) permits every real c, including negative c. *)
Lemma representing_density_set_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R)
    (k : X -> R) (E : set X) (s : X -> R) (c : R) :
  is_real_lattice_density mu (total_scalar_lp mu 1) A k ->
  is_characteristic_function E s -> measure_measurable mu E -> mu E < +oo ->
  (forall x, E x -> (k x<=c)%R) -> (A s)%:E<=c%:E*mu E.
Proof.
move=> hk hs hE hf hkc.
have hfin : mu E \is a fin_num by rewrite ge0_fin_numE ?hf //; exact (@measure_nonnegative R X mu hm E).
have hi : is_measure_integral mu (real_total_integrand s) (fine (mu E))%:E.
  rewrite fineK //; exact (@measure_characteristic_integral R X mu hm E s hs hE).
have hc := @real_total_integral_scale R X mu hm s (fine (mu E)) c hi.
have hks := hk.2 s (@finite_characteristic_total_lone R X mu hm E s hs hE hf).
rewrite -[mu E](fineK hfin) -EFinM.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hks hc).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (s x*k x)%:E,(c*s x)%:E; split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin; case: (pselect (E x))=> hx.
- by rewrite (characteristic_on_set hs hx) mul1r mulr1; exact: hkc.
- by rewrite (characteristic_off_set hs hx) mul0r mulr0.
Qed.

(** Source for [representing_density_set_lower_bound]:
    supporting lower test for the vertical part of
    Federer 2.5.10, p. 101. If c<=k on E,
    then c*mu(E) is at most its characteristic pairing,
    by 2.4.4(5), p. 82. *)
Lemma representing_density_set_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R)
    (k : X -> R) (E : set X) (s : X -> R) (c : R) :
  is_real_lattice_density mu (total_scalar_lp mu 1) A k ->
  is_characteristic_function E s -> measure_measurable mu E -> mu E < +oo ->
  (forall x, E x -> (c<=k x)%R) -> c%:E*mu E<=(A s)%:E.
Proof.
move=> hk hs hE hf hck.
have hfin : mu E \is a fin_num by rewrite ge0_fin_numE ?hf //; exact (@measure_nonnegative R X mu hm E).
have hi : is_measure_integral mu (real_total_integrand s) (fine (mu E))%:E.
  rewrite fineK //; exact (@measure_characteristic_integral R X mu hm E s hs hE).
have hc := @real_total_integral_scale R X mu hm s (fine (mu E)) c hi.
have hks := hk.2 s (@finite_characteristic_total_lone R X mu hm E s hs hE hf).
rewrite -[mu E](fineK hfin) -EFinM.
apply: (@measure_integral_monotone R X mu hm _ _ _ _ hc hks).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exists (c*s x)%:E,(s x*k x)%:E; split; first by apply/real_total_integrand_graph.
split; first by apply/real_total_integrand_graph.
rewrite lee_fin; case: (pselect (E x))=> hx.
- by rewrite (characteristic_on_set hs hx) mul1r mulr1; exact: hck.
- by rewrite (characteristic_off_set hs hx) mul0r mulr0.
Qed.
