(** Quotient used to repair the spherical covering argument for Federer
    (1969), 2.10.19(3)–(5), p. 181. The corrected quotient is local to these
    covering arguments; metric densities themselves use positive finite
    radius normalisations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CaratheodoryDensityQuotient CaratheodoryDensityFunction
  CaratheodoryDensityLargeCells ExtendedRealConventions PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_measure_cost_ratio]: supporting corrected
    mu(S)/zeta(S) for the covering step in 2.10.19, p. 181 Original
    arithmetic is unchanged. *)
Definition caratheodory_measure_cost_ratio (R : realType) (X : Type)
    (mu c : set X -> \bar R) := caratheodory_density_function mu c setT.

(** Source for [caratheodory_measure_cost_ratio_graph]: supporting numerator
    evaluation in the repaired covering step for 2.10.19, p. 181 *)
Lemma caratheodory_measure_cost_ratio_graph (R : realType) (X : Type)
    (mu c : set X -> \bar R) S y :
  partial_function_graph (caratheodory_measure_cost_ratio mu c) S y <->
  caratheodory_density_divide (mu S) (c S)=Some y.
Proof. by rewrite /caratheodory_measure_cost_ratio /caratheodory_density_function /= setTI. Qed.

(** Source for [caratheodory_density_divide_large]: supporting strict
    good-cell estimate with zero costs in 2.10.19, p. 181 A positive
    threshold cannot be exceeded by a defined quotient with infinite
    denominator. *)
Lemma caratheodory_density_divide_large (R : realType) (x c y : \bar R) (t : R) :
  0<=x -> 0<=c -> (0<t)%R ->
  caratheodory_density_divide x c=Some y -> t%:E<y -> t%:E*c<x.
Proof.
move=> hx hc ht.
case: (eqVneq c 0)=> [->|hcn].
- case: (eqVneq x 0)=> [->|hxn].
  + rewrite caratheodory_density_divide_zero_zero=> -[<-] hy.
    have hn : 0<t%:E by rewrite lte_fin.
    by have := lt_trans hn hy; rewrite ltxx.
  + have hp : 0<x by rewrite lt_def hxn hx.
    rewrite (caratheodory_density_divide_positive_zero hp)=> _ _; by rewrite mule0.
- have hp : 0<c by rewrite lt_def hcn hc.
  case: (ltP c +oo)=> [hcf|hcif].
  + rewrite (caratheodory_density_divide_nonzero x hcn)=> hdiv hy.
    exact: positive_finite_quotient_large hp hcf hdiv hy.
  + have he : c=+oo by apply/eqP; rewrite eq_le leey hcif.
    rewrite he /caratheodory_density_divide /= /extended_divide /=.
    case: x hx=> [a| |] hx //=.
    rewrite ?invey ?mule0 ?mulr0=> -[<-] hy.
    have hn : 0<t%:E by rewrite lte_fin.
    by have := lt_trans hn hy; rewrite ltxx.
Qed.
