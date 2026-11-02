(** Corrected density function for Federer (1969), 2.10.17(2), p. 179. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP CaratheodoryDensityQuotient MeasureUP
  MetricDiameter CoveringRelationUP CoveringRelationLimits ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_function]: corrected function mu(A
    intersect S)/zeta(S) for 2.10.17(2), p. 179. *)
Definition caratheodory_density_function (R : realType) (X : Type)
    (mu : set X -> \bar R) (c : set X -> \bar R) (A : set X) :
    partial_function (set X) (\bar R).
Proof.
refine (@Build_partial_function (set X) (\bar R)
  (fun S y => caratheodory_density_divide (mu (A `&` S)) (c S)=Some y) _).
move=> S y z hy hz; rewrite hy in hz; by case: hz.
Defined.

(** Source for [caratheodory_density_function_graph]: supporting exact
    quotient graph for the corrected 2.10.17, p. 179 *)
Lemma caratheodory_density_function_graph (R : realType) (X : Type)
    (mu : set X -> \bar R) (c : set X -> \bar R) (A S : set X) y :
  partial_function_graph (caratheodory_density_function mu c A) S y <->
    caratheodory_density_divide (mu (A `&` S)) (c S)=Some y.
Proof. by []. Qed.

(** Source for [caratheodory_density_upper_local_estimate]: supporting
    passage from the strict upper density hypothesis to a uniform
    small-generator estimate in 2.10.17(2), p. 179. infinite costs make the
    bound automatic. No fineness or measurability of A is needed here. *)
Theorem caratheodory_density_upper_local_estimate (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : set X -> \bar R)
    (C : X -> set X -> Prop) (A : set X) (x : X) (t : R) :
  (0<t)%R -> (forall S, C x S -> 0<=c S) ->
  covering_upper_limit C (caratheodory_density_function mu c A) x<t%:E ->
  exists delta : \bar R, 0<delta /\ forall S, C x S ->
    extended_metric_diameter S<=delta -> mu (A `&` S)<=t%:E*c S.
Proof.
move=> ht hc hlim.
have [e [he hs]] := (covering_upper_limit_lt_iff _ _ _ _).1 hlim.
have heh : (0<e/2)%R by lra.
have hehalf : (e/2<e)%R by lra.
have hsmall : (e/2)%R%:E<e%:E by rewrite lte_fin.
exists (e/2)%R%:E; split; first by rewrite lte_fin.
move=> S hC hdiam.
case: (ltP (c S) +oo)=> [hcf|hcfin].
- have hx := @measure_nonnegative R X mu hm (A `&` S).
  have [z hz] := caratheodory_density_divide_finite_denominator hx (hc S hC) hcf.
  have hgraph : partial_function_graph (caratheodory_density_function mu c A) S z := hz.
  have hrange : covering_value_range C (caratheodory_density_function mu c A) x e z.
    exists S; split=> //; split=> //; exact: le_lt_trans hdiam hsmall.
  have hzle := extended_real_sup_upper hrange.
  have hzt : z<=t%:E := ltW (le_lt_trans hzle hs).
  exact: caratheodory_density_finite_cost_bound hx (hc S hC) hcf hz hzt.
- have hcinf : c S = +oo by apply/eqP; rewrite eq_le leey hcfin.
  have htE : 0<t%:E by rewrite lte_fin.
  by rewrite hcinf (gt0_muley htE) leey.
Qed.
