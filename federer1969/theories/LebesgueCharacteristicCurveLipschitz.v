(** Federer (1969), 2.9.23, p. 168: g(x)=chi_(0,x) vanishes for x<=0, its L1
    increments have length v-u when 0<=u<v, and its sharp Lipschitz constant
    is one. The supporting integral laws are 2.4.4, p. 82, and 2.4.12, p.
    86. The local Federer erratum has no entry for pp. 168–169. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal lra.
From Federer Require Import RealNormUP MeasureUP MeasureIntegralUniqueness
  CharacteristicFunctionUP CharacteristicFunctionSealed FiniteMeasureCharacteristicLp
  TotalScalarPairing SummableRealFunctionUP SummableRealSpace SummableRealSeminorm SummableRealIntegralMap
  LebesgueScalarMeasure LebesgueIntervalCharacteristics.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_nonnegative_integral_seminorm]: supporting
    identity integral f=phi_(1)(f) for f>=0 in Federer
    2.9.23, p. 168, by the definition in 2.4.12, p. 86. *)
Lemma summable_nonnegative_integral_seminorm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : summable_real_space hm) :
  (forall t, 0<=summable_real_value f t) ->
  summable_real_integral_map f=summable_real_seminorm f.
Proof.
move=> hf.
have hi := @total_scalar_lone_absolute_integral R X mu hm
  (summable_real_value f) (summable_real_value_lone f).
have he : (fun t => `|summable_real_value f t|)=summable_real_value f.
  by apply: funext=> t; rewrite ger0_norm.
rewrite he in hi.
exact: EFin_inj (measure_integral_unique (summable_real_integral_map_specification f) hi).
Qed.

(** Source for [lebesgue_characteristic_curve_integral]: supporting
    actual scalar integral of g(x) in Federer 2.9.23,
    p. 168, equal to max(x,0). *)
Lemma lebesgue_characteristic_curve_integral (R : realType) (x : R) :
  summable_real_integral_map (lebesgue_characteristic_curve x)=Num.max x 0.
Proof.
have hi := summable_real_integral_map_specification (lebesgue_characteristic_curve x).
rewrite lebesgue_characteristic_curve_value in hi.
exact: EFin_inj (measure_integral_unique hi (lebesgue_interval_characteristic_integral x)).
Qed.

(** Source for [lebesgue_characteristic_curve_order]: supporting
    pointwise nesting chi_(0,u)<=chi_(0,v) when u<=v,
    for the increment formula in Federer 2.9.23, p. 168. *)
Lemma lebesgue_characteristic_curve_order (R : realType) (u v : R) :
  u<=v -> forall t,
    summable_real_value (lebesgue_characteristic_curve u) t<=
    summable_real_value (lebesgue_characteristic_curve v) t.
Proof.
move=> huv t; rewrite !lebesgue_characteristic_curve_value.
have hu := @CharacteristicFunction.laws R R `]0,u[.
have hv := @CharacteristicFunction.laws R R `]0,v[.
case: (pselect (`]0,u[ t))=> ht.
- have ht' : `]0,v[ t.
    move: ht; rewrite /= !in_itv /= => /andP[h0 htu].
    by rewrite h0 (lt_le_trans htu huv).
  by rewrite (characteristic_on_set hu ht) (characteristic_on_set hv ht').
- rewrite (characteristic_off_set hu ht).
  exact: (total_characteristic_nonnegative hv t).
Qed.

(** Source for [lebesgue_characteristic_curve_increment]: direct
    L1 distance formula in Federer 2.9.23, p. 168,
    extended to all ordered real endpoints by positive parts. *)
Lemma lebesgue_characteristic_curve_increment (R : realType) (u v : R) :
  u<=v -> summable_real_seminorm
    (lebesgue_characteristic_curve v-lebesgue_characteristic_curve u)=
    Num.max v 0-Num.max u 0.
Proof.
move=> huv.
rewrite -summable_nonnegative_integral_seminorm.
- by rewrite linearB /= !lebesgue_characteristic_curve_integral.
- move=> t; rewrite linearB /= !fctE subr_ge0.
  exact: lebesgue_characteristic_curve_order.
Qed.

(** Source for [lebesgue_characteristic_curve_positive_increment]:
    direct printed formula phi_(1)(g(u)-g(v))=v-u for
    0<=u<v in Federer 2.9.23, p. 168. The equal-
    endpoint case is included as a regression boundary. *)
Lemma lebesgue_characteristic_curve_positive_increment (R : realType) (u v : R) :
  0<=u -> u<=v -> summable_real_seminorm
    (lebesgue_characteristic_curve u-lebesgue_characteristic_curve v)=v-u.
Proof.
move=> hu huv; rewrite (real_seminorm_subtract (summable_real_seminorm_laws _))
  lebesgue_characteristic_curve_increment //.
by rewrite (max_l (le_trans hu huv)) (max_l hu).
Qed.

(** Source for [lebesgue_characteristic_curve_lipschitz]: direct
    upper Lipschitz bound one in Federer 2.9.23, p. 168,
    including pairs on opposite sides of zero and negative pairs. *)
Lemma lebesgue_characteristic_curve_lipschitz (R : realType) (u v : R) :
  summable_real_seminorm (lebesgue_characteristic_curve v-lebesgue_characteristic_curve u)<=`|v-u|.
Proof.
have hN := summable_real_seminorm_laws (lebesgue_scalar_is_measure R).
wlog huv : u v / u<=v.
  move=> h; case: (leP u v)=> huv; first exact: h huv.
  rewrite (real_seminorm_subtract hN) distrC; exact: h (ltW huv).
have hd : 0<=v-u by rewrite subr_ge0.
rewrite lebesgue_characteristic_curve_increment // (ger0_norm hd).
case: (leP v 0)=> hv; case: (leP u 0)=> hu; lra.
Qed.

(** Source for [lebesgue_characteristic_curve_lipschitz_sharp]: direct
    sharpness of Lip(g) = 1 in Federer 2.9.23, p. 168.
    The pair 0,1 forces every proposed bound to be at least one. *)
Lemma lebesgue_characteristic_curve_lipschitz_sharp (R : realType) (L : R) :
  (forall u v : R, summable_real_seminorm
    (lebesgue_characteristic_curve v-lebesgue_characteristic_curve u)<=L*`|v-u|) -> 1<=L.
Proof.
move=> h; have hh := h 1 0.
by rewrite lebesgue_characteristic_curve_positive_increment ?ler01 //
  subr0 sub0r normrN normr1 mulr1 in hh.
Qed.
