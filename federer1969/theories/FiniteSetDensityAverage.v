(** Federer (1969), 2.5.7, p. 99: the normalized integrals phi(A_j)^(-1)
    integral_(A_j) u in tau for q=infinity. We use sealed characteristic
    functions and the sealed product integral; the formula is specified only
    on such measurable sets and L-infinity densities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP CharacteristicFunctionUP CharacteristicFunctionSealed
  SummableRealFunctionUP TotalScalarLpUP TotalScalarLpFiniteSeminorm TotalScalarPairingValue
  TotalLpPairingBound LpConjugatePair FiniteMeasureCharacteristicLp PositivePairingAlmostOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_set_density_average]: the normalized covering-set
    integral in Federer 2.5.7, p. 99 The finite projection of the measure is
    exact on the stated positive finite-mass domain. *)
Definition finite_set_density_average (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A : set X) (u : X -> R) : R :=
  (total_scalar_pairing mu (@CharacteristicFunction.value R X A) u / fine (mu A))%R.

(** Source for [finite_set_density_average_bounds]: the estimate
    0<=phi(A_j)^(-1) integral_(A_j) u<=M in Federer 2.5.7, p. 99 Summability
    is obtained from the proved L1/L-infinity pairing. *)
Lemma finite_set_density_average_bounds (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (u : X -> R) (M : R) :
  measure_measurable mu A -> 0 < mu A < +oo -> total_scalar_lp mu +oo u ->
  (forall x, (0 <= u x)%R) -> total_scalar_lp_norm mu +oo u <= M%:E ->
  (0 <= finite_set_density_average mu A u <= M)%R.
Proof.
move=> hA /andP [hA0 hAfin] hu hu0 hb.
have hfin : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hmass : mu A=(fine (mu A))%:E by rewrite fineK.
have hb0 : (0 < fine (mu A))%R by move: hA0; rewrite hmass lte_fin.
pose s := @CharacteristicFunction.value R X A.
have hs : is_characteristic_function A s := @CharacteristicFunction.laws R X A.
have [hsl hsn] := @finite_measure_characteristic_lone R X mu hm A s _ hs hA hmass.
have hpq : @is_lp_conjugate_pair R 1 +oo by right; left.
have [hi hj] := @total_lp_pairing_specification_and_bound R X mu hm 1 +oo s u hpq hsl hu.
have hj0 := @nonnegative_total_pairing_value R X mu hm s u
  (ex_intro _ (total_scalar_pairing mu s u) hi) (total_characteristic_nonnegative hs) hu0.
have hNu : (finite_total_scalar_lp_norm mu +oo u <= M)%R.
  by rewrite -(@finite_total_scalar_lp_norm_exact R X mu hm +oo u hu) lee_fin in hb.
rewrite /finite_set_density_average; change (is_true (0 <= total_scalar_pairing mu s u / fine (mu A) <= M)%R).
apply/andP; split; first exact: divr_ge0 hj0 (ltW hb0).
rewrite ler_pdivrMr //.
rewrite hsn (ger0_norm hj0) in hj.
apply: le_trans hj _; rewrite mulrC; apply: (ler_wpM2r (ltW hb0)); exact: hNu.
Qed.

(** Source for [finite_set_density_average_almost_order]: monotonicity of
    each coordinate of tau in Federer 2.5.7, p. 99 *)
Lemma finite_set_density_average_almost_order (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (u v : X -> R) :
  measure_measurable mu A -> 0 < mu A < +oo ->
  total_scalar_lp mu +oo u -> total_scalar_lp mu +oo v ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  (finite_set_density_average mu A u <= finite_set_density_average mu A v)%R.
Proof.
move=> hA /andP [hA0 hAfin] hu hv huv.
have hfin : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hmass : mu A=(fine (mu A))%:E by rewrite fineK.
have hb0 : (0 < fine (mu A))%R by move: hA0; rewrite hmass lte_fin.
pose s := @CharacteristicFunction.value R X A.
have hs : is_characteristic_function A s := @CharacteristicFunction.laws R X A.
have [hsl _] := @finite_measure_characteristic_lone R X mu hm A s _ hs hA hmass.
have hpq : @is_lp_conjugate_pair R 1 +oo by right; left.
rewrite /finite_set_density_average ler_pM2r ?invr_gt0 //.
exact: (@positive_lp_pairing_almost_order R X mu hm 1 +oo s u v hpq hsl hu hv
  (total_characteristic_nonnegative hs) huv).
Qed.

(** Source for [finite_set_density_average_equality]: equality of an ordered
    pair of coordinates forces almost equality on the covering set,
    supporting strictness of tau in Federer 2.5.7, p. 99 *)
Lemma finite_set_density_average_equality (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (u v : X -> R) :
  measure_measurable mu A -> 0 < mu A < +oo ->
  total_scalar_lp mu +oo u -> total_scalar_lp mu +oo v ->
  measure_almost_everywhere mu [set x | (u x <= v x)%R] ->
  finite_set_density_average mu A u=finite_set_density_average mu A v ->
  measure_almost_everywhere mu [set x | A x -> u x=v x].
Proof.
move=> hA /andP [hA0 hAfin] hu hv huv he.
have hfin : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
have hmass : mu A=(fine (mu A))%:E by rewrite fineK.
have hb0 : (0 < fine (mu A))%R by move: hA0; rewrite hmass lte_fin.
pose s := @CharacteristicFunction.value R X A.
have hs : is_characteristic_function A s := @CharacteristicFunction.laws R X A.
have [hsl _] := @finite_measure_characteristic_lone R X mu hm A s _ hs hA hmass.
apply: (@ordered_characteristic_pairing_equality R X mu hm A s u v hs hsl hu hv
  (total_characteristic_nonnegative hs) huv).
have hh := congr1 (fun t : R => (t*fine (mu A))%R) he.
by rewrite /finite_set_density_average !divfK ?gt_eqF // in hh.
Qed.
