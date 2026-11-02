(** Federer (1969), 2.4.17, p. 90: the map u |-> log phi_(1/u)(f) is convex
    on U. Reciprocal exponent zero uses the separately proved infinity
    endpoint estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic RealPowerLogarithm
  MeasureUP MeasurableFunctionUP ConvexFunctionUP MeasureExponentDomain
  MeasureReciprocalInterval MeasureReciprocalInterpolation MeasurePartialReciprocalInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_reciprocal_log_norm_convex]: the convex function
    assertion of Federer 2.4.17, p. 90 The domain is exactly the positive
    finite norms within 0<=u<=1, with the infinity convention at zero.
    Conull partial domains are retained through the proved total-extension
    reduction. *)
Theorem measure_reciprocal_log_norm_convex (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : PartialFunctionUP.partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f ->
  @is_real_convex_function_on R R^o
    (measure_positive_reciprocal_exponents mu f)
    (measure_reciprocal_log_norm mu f).
Proof.
move=> hf; have hconv := @measure_partial_positive_reciprocal_convex R X mu hm f hf.
split=> //; move=> u v hu hv t ht ht1.
change ((measure_reciprocal_log_norm mu f ((1-t) * u+t * v)%R <=
  (1-t) * measure_reciprocal_log_norm mu f u+
  t * measure_reciprocal_log_norm mu f v)%R).
have [ht0|ht0] := eqVneq t 0%R.
- by rewrite ht0 subr0 !mul1r !mul0r !addr0.
have [htone|htone] := eqVneq t 1%R.
- by rewrite htone subrr !mul0r !mul1r !add0r.
have [huv|huv] := eqVneq u v.
- by rewrite huv -!mulrDl subrK !mul1r.
have htpos : (0 < t)%R by rewrite lt_neqAle eq_sym ht0 ht.
have htop : (t < 1)%R by rewrite lt_neqAle htone ht1.
have hat : (0 < 1-t)%R by rewrite subr_gt0.
have hab : (1-t+t= 1)%R by rewrite subrK.
have hw := hconv u v hu hv t ht ht1.
move: hu=> [hu0 [hu1 [hup huf]]]; move: hv=> [hv0 [hv1 [hvp hvf]]].
move: hw=> [hw0 [hw1 [hwp hwf]]].
pose A := fine (measure_reciprocal_exponent_norm mu f u).
pose B := fine (measure_reciprocal_exponent_norm mu f v).
pose C := fine (measure_reciprocal_exponent_norm mu f ((1-t) * u+t * v)%R).
have hAfin : measure_reciprocal_exponent_norm mu f u \is a fin_num.
  by rewrite (ge0_fin_numE (ltW hup)).
have hBfin : measure_reciprocal_exponent_norm mu f v \is a fin_num.
  by rewrite (ge0_fin_numE (ltW hvp)).
have hCfin : measure_reciprocal_exponent_norm mu f ((1-t) * u+t * v)%R \is a fin_num.
  by rewrite (ge0_fin_numE (ltW hwp)).
have hA : measure_reciprocal_exponent_norm mu f u=A%:E by rewrite /A fineK.
have hB : measure_reciprocal_exponent_norm mu f v=B%:E by rewrite /B fineK.
have hC : measure_reciprocal_exponent_norm mu f ((1-t) * u+t * v)%R=C%:E by rewrite /C fineK.
have hApos : (0 < A)%R by move: hup; rewrite hA lte_fin.
have hBpos : (0 < B)%R by move: hvp; rewrite hB lte_fin.
have hCpos : (0 < C)%R by move: hwp; change (0 < measure_reciprocal_exponent_norm mu f ((1-t) * u+t * v)%R -> (0 < C)%R); rewrite hC lte_fin.
have hne : u <> v by move=> he; move: huv; rewrite he eqxx.
have hbnd := @measure_reciprocal_interpolation R X mu hm u v (1-t)%R t A B f
  hu0 hu1 hv0 hv1 hne hat htpos hab hApos hBpos hf hA hB.
rewrite hC lee_fin in hbnd.
exact: (@real_logarithm_interpolation_bound R A B C (1-t)%R t hApos hBpos hCpos hbnd).
Qed.
