(** Federer (1969), 2.9.23, pp. 168–169: the L1-valued curve g(x)=chi_(0,x)
    has Lipschitz constant one but no derivative at any positive point; even
    its difference quotients have no weak limit. We use the printed seminorm
    convention of 2.4.12, pp. 86–87. The stronger weak-limit assertion is
    proved using characteristic tests on shrinking intervals and absolute
    continuity of the candidate's L1 integral, instead of leaving the last
    contradiction as 'absurd'. The local Federer erratum has no entry for
    pp. 168–169. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import RealNormUP RealCurveDerivativeUP NormedCurveDerivativeUP
  SeminormWeakLimitUP LebesgueScalarMeasure SummableRealSpace SummableRealSeminorm
  SummableCharacteristicFunctional SummableCharacteristicSmallSets
  LebesgueIntervalCharacteristics LebesgueCharacteristicCurveLipschitz
  LebesgueCharacteristicQuotients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_characteristic_quotients_no_weak_limit]: direct
    last assertion of Federer 2.9.23, p. 169. For a proposed
    limit v, choose one small fixed interval [x,x+d]; its integral
    on v has absolute value below 1/2, but its value on every
    sufficiently small positive difference quotient is one. *)
Theorem lebesgue_characteristic_quotients_no_weak_limit (R : realType) (x : R)
    (v : summable_real_space (lebesgue_scalar_is_measure R)) : 0<x ->
  ~ punctured_seminorm_weak_limit (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
    (lebesgue_characteristic_quotient x) v.
Proof.
move=> hx hw.
have he : (0<1/2 :> R) by rewrite divr_gt0 // ltr0n.
have [d [hd hsmall]] := @summable_characteristic_small_sets R R
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) v (1/2) he.
pose hA := lebesgue_closed_test_interval_measurable x (x+d).
have hmA : (lebesgue_scalar_measure `[x,(x+d)%R]<=d%:E)%E.
  rewrite lebesgue_scalar_segment; last by lra.
  have heq : x+d-x=d by lra.
  by rewrite heq.
have hAv := hsmall _ hA hmA.
have hW := hw (summable_characteristic_functional hA)
  (@summable_characteristic_functional_bounded R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) `[x,x+d] hA).
have he4 : (0<1/4 :> R) by rewrite divr_gt0 // ltr0n.
have [delta [hdelta hq]] := hW (1/4) he4.
pose h := Num.min delta d/2.
have hmin : 0<Num.min delta d by rewrite lt_min hdelta hd.
have hh : 0<h by rewrite /h divr_gt0 // ltr0n.
have hless : h<Num.min delta d by rewrite /h; lra.
have hmd : Num.min delta d<=delta by rewrite ge_min lexx.
have hmr : Num.min delta d<=d by rewrite ge_min lexx orbT.
have hcut : 0<`|h|<delta.
  rewrite (ger0_norm (ltW hh)); apply/andP; split=> //.
  exact: lt_le_trans hless hmd.
have hhr : h<=d := ltW (lt_le_trans hless hmr).
have hnear := hq h hcut.
change (is_true (`|summable_characteristic_functional hA (lebesgue_characteristic_quotient x h)-
  summable_characteristic_functional hA v|<1/4)) in hnear.
rewrite /hA (lebesgue_characteristic_quotient_test hx hh hhr) in hnear.
move: hAv hnear; rewrite !ltr_norml=> /andP[h1 h2] /andP[h3 h4].
lra.
Qed.

(** Source for [lebesgue_characteristic_curve_no_derivative]: direct
    failure of an L1 derivative at each x>0 in Federer 2.9.23,
    p. 169. Seminorm convergence would imply convergence under
    every bounded linear test, contradicting the stronger result. *)
Theorem lebesgue_characteristic_curve_no_derivative (R : realType) (x : R)
    (v : summable_real_space (lebesgue_scalar_is_measure R)) : 0<x ->
  ~ has_normed_curve_derivative (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
    (@lebesgue_characteristic_curve R) x v.
Proof.
move=> hx hD; apply (@lebesgue_characteristic_quotients_no_weak_limit R x v hx).
exact (@punctured_seminorm_limit_weak R (summable_real_space (lebesgue_scalar_is_measure R))
  (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
  (lebesgue_characteristic_quotient x) v
  (real_seminorm_nonnegative (summable_real_seminorm_laws (lebesgue_scalar_is_measure R))) hD).
Qed.

(** Source for [federer_2_9_23]: complete counterexample of Federer
    2.9.23, pp. 168–169: the printed characteristic curve,
    vanishing on the negative half-line, exact positive increments,
    sharp Lipschitz constant one, and absence of even a weak
    difference-quotient limit at every positive point. *)
Theorem federer_2_9_23 (R : realType) :
  (forall x : R, x<=0 -> lebesgue_characteristic_curve x=0) /\
  (forall u v : R, 0<=u -> u<=v -> summable_real_seminorm
    (lebesgue_characteristic_curve u-lebesgue_characteristic_curve v)=v-u) /\
  (forall u v : R, summable_real_seminorm
    (lebesgue_characteristic_curve v-lebesgue_characteristic_curve u)<=`|v-u|) /\
  (forall L : R, (forall u v : R, summable_real_seminorm
    (lebesgue_characteristic_curve v-lebesgue_characteristic_curve u)<=L*`|v-u|) -> 1<=L) /\
  (forall (x : R) (v : summable_real_space (lebesgue_scalar_is_measure R)), 0<x ->
    ~ punctured_seminorm_weak_limit (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
      (lebesgue_characteristic_quotient x) v /\
    ~ has_normed_curve_derivative (@summable_real_seminorm R R _ (lebesgue_scalar_is_measure R))
      (@lebesgue_characteristic_curve R) x v).
Proof.
split; first exact: lebesgue_characteristic_curve_nonpositive.
split; first exact: lebesgue_characteristic_curve_positive_increment.
split; first exact: lebesgue_characteristic_curve_lipschitz.
split; first exact: lebesgue_characteristic_curve_lipschitz_sharp.
move=> x v hx; split.
- exact: lebesgue_characteristic_quotients_no_weak_limit.
- exact: lebesgue_characteristic_curve_no_derivative.
Qed.
