(** Federer (1969), 2.5.9, p. 100: supporting localization for almost
    uniqueness of the density. Corrected positive density (erratum p. 2,
    book p. 100 line 22) and dominated convergence 2.4.9, p. 85, extend zero
    pairings to measurable pieces of positive lattice tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasurableFunctionUP
  FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureIntegralUP SummableRealFunctionUP TotalScalarLpUP TotalScalarLpCharacteristic
  CharacteristicFunctionUP RegularLatticeLoneDensity PositiveLatticeAlmostApproximation DominatedZeroPairingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_zero_pairing_characteristic_piece]:
    supporting localization of the almost-uniqueness assertion in
    Federer 2.5.9, p. 100. The arbitrary measurable
    weight need not have finite essential norm. *)
Theorem lattice_zero_pairing_characteristic_piece (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (w : X -> R) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  is_measure_measurable_function mu (total_scalar_function w) ->
  (forall h, L h -> is_measure_integral mu (real_total_integrand (fun x => (h x*w x)%R)) 0) ->
  forall f E s, positive_function_lattice L f -> measure_measurable mu E ->
    is_characteristic_function E s ->
    is_measure_integral mu (real_total_integrand (fun x => (f x*s x*w x)%R)) 0.
Proof.
move=> hrep hr hw hzero f E s hf hE hs.
have hfm := @represented_lattice_in_total_lone R X mu hm L F hrep f hf.1.
have hg := (@positive_lp_characteristic_pieces R X mu hm 1 E s f hs hE (conj hfm hf.2)).1.
have hgf x : (f x*s x <= f x)%R.
  case: (pselect (E x))=> hx.
  - by rewrite (characteristic_on_set hs hx) mulr1.
  - by rewrite (characteristic_off_set hs hx) mulr0; exact: hf.2.
have [u [hu hlim]] := @regular_positive_lattice_almost_approximation R X L hL F mu hm hrep hr
  f (fun x => (f x*s x)%R) hf hg hgf.
have hbound n x : (0 <= u n x <= f x)%R by apply/andP; split; [exact: (hu n).1.2|exact: (hu n).2].
apply: (@dominated_zero_pairing_limit R X mu hm u f (fun x => (f x*s x)%R) w
  hbound hf.2 hg.1.2.1 hw _ _ hlim).
- exists 0%R; exact: hzero f hf.1.
- move=> n; exact: hzero _ (hu n).1.1.
Qed.
