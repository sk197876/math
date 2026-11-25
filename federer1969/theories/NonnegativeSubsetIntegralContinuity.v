(** Federer (1969), 2.9.20, p. 166: use 2.4.11 for the integral of |g'| on
    small measurable subsets of a fixed segment. This supporting nonnegative
    formulation follows 2.4.11, pp. 85–86. Source context:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialAbsolutePartsGraph MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralAbsoluteContinuity MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_partial_absolute_graph]: supporting idempotence
    of the absolute value on |g'| in Federer 2.9.20, p. 166 This graph law
    preserves a possibly partial domain and allows positive infinity. *)
Lemma nonnegative_partial_absolute_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :
  (forall x y, partial_function_graph f x y -> 0<=y) -> forall x y,
  partial_function_graph (partial_extended_function_absolute_value f) x y <->
    partial_function_graph f x y.
Proof.
move=> hpos x y; split.
- move=> [z [hz he]]; have hzpos := hpos x z hz.
  by rewrite (gee0_abs hzpos) in he; rewrite -he.
- move=> hy; exists y; split=> //; exact: gee0_abs (hpos x y hy).
Qed.

(** Source for [nonnegative_subset_integral_small_sets]: supporting
    application of Federer 2.4.11 in 2.9.20, p. 166 A nonnegative partial
    function with a finite integral on B has uniformly small finite
    integrals on measurable A contained in B. No finite measure hypothesis
    on the ambient space or total integrand domain is added. *)
Theorem nonnegative_subset_integral_small_sets (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R))
    (B : set X) (I e : R) : is_measure mu ->
  (forall x y, partial_function_graph f x y -> 0<=y) ->
  is_measure_subset_integral mu B f I%:E -> (0<e)%R ->
  exists d : R, (0<d)%R /\ forall A : set X,
    measure_measurable mu A -> A `<=` B -> mu A<=d%:E ->
    exists J : R, is_measure_subset_integral mu A f J%:E /\ (J<e)%R.
Proof.
move=> hm hpos hI he.
pose FB := partial_function_zero_extension (0 : extended_real_line R) B f.
have hsum : is_measure_summable mu FB by exists I.
have hFBpos : forall x y, partial_function_graph FB x y -> 0<=y.
  move=> x y hy; have [[hx hf]|[_ ->]] :=
    (partial_function_zero_extension_graph 0 B f x y).1 hy; last exact: lexx.
  exact: hpos x y hf.
have [d [hd hsmall]] := @measure_integral_absolute_continuity R X mu hm FB e hsum he.
exists d; split=> // A hA hAB hAd.
have [J [hJ hJe]] := hsmall A hA hAd.
exists J; split=> //.
apply: (@measure_integral_graph_equivalent R X mu _ _ J%:E _ hJ)=> x y.
rewrite !partial_function_zero_extension_graph; split.
- move=> [[hx hy]|hzero]; last by right.
  have hFB := (@nonnegative_partial_absolute_graph R X FB hFBpos x y).1 hy.
  left; split=> //.
  exact: (@partial_function_zero_extension_on X (extended_real_line R) 0 B f x y (hAB x hx)).1 hFB.
- move=> [[hx hy]|hzero]; last by right.
  left; split=> //.
  apply/(@nonnegative_partial_absolute_graph R X FB hFBpos x y).
  exact: (@partial_function_zero_extension_on X (extended_real_line R) 0 B f x y (hAB x hx)).2 hy.
Qed.
