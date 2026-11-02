(** Supporting positive-power measurability for Federer (1969), 2.10.5, p.
    172: projected volumes can be infinite on unbounded Suslin sets. The
    finite-exponent formula of 2.4.12, p. 86, therefore needs nonnegative
    extended inputs here. Retain infinity and use the local order-ray
    criterion of 2.3.2(2), p. 73. it does not state this extended-input
    supporting lemma. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower ExtendedPositivePowerOrder
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableExtendedRationalRays
  CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_power_upper_threshold]: supporting
    inverse-power threshold law for the integral-root
    formula used in Federer 2.10.5, p. 172,
    from 2.4.12, p. 86. Both the argument
    and the threshold can be positive infinity. *)
Lemma extended_power_upper_threshold (R : realType) (x a : \bar R) (p : R) :
  0<=x -> 0<=a -> (0<p)%R ->
  (a<extended_positive_power x p)=(extended_positive_power a p^-1<x).
Proof.
move=> hx ha hp.
have hi : (0<p^-1)%R by rewrite invr_gt0.
have he := @extended_positive_power_strict_order R a (extended_positive_power x p)
  p^-1 ha (extended_positive_power_nonnegative x p) hi.
by rewrite extended_positive_power_root_cancel // in he; exact: esym he.
Qed.

(** Source for [measurable_nonnegative_extended_power]:
    supporting measurability of f_S raised to a
    positive exponent in Federer 2.10.5, p. 172.
    Its total nonnegative argument is extended-valued;
    no finiteness assumption or discarded infinite
    level set is hidden in a scalar projection. *)
Theorem measurable_nonnegative_extended_power (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (p : R) :
  (forall x, 0<=f x) -> (0<p)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  @is_measure_measurable_function R X (extended_real_line R) mu
    (partial_function_total (fun x => extended_positive_power (f x) p)).
Proof.
move=> hf0 hp hf.
have hd : measure_almost_everywhere mu (partial_function_domain
    (partial_function_total (fun x => extended_positive_power (f x) p))).
  rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
apply: (proj2 (@measurable_extended_rational_upper_rays_iff R X mu hm _ hd))=> q.
rewrite partial_function_total_preimage.
case: (leP 0 (ratr q : R)%:E)=> hq.
- have he : (fun x => extended_positive_power (f x) p) @^-1`
      [set y | (ratr q : R)%:E<y] =
      f @^-1` [set y | extended_positive_power (ratr q : R)%:E p^-1<y].
    apply/seteqP; split=> x; rewrite /preimage /=
      extended_power_upper_threshold //; by [].
  rewrite he -partial_function_total_preimage.
  apply: (@measurable_function_open_preimage R X (extended_real_line R)
    mu (partial_function_total f) hf).
  exact: order_strict_upper_ray_open.
- have he : (fun x => extended_positive_power (f x) p) @^-1`
      [set y | (ratr q : R)%:E<y] = setT.
    apply/seteqP; split=> x _; first exact I.
    exact: lt_le_trans hq (extended_positive_power_nonnegative (f x) p).
  rewrite he; exact: measure_measurable_whole hm.
Qed.
