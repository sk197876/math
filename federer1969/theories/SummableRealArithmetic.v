(** Federer (1969), 2.5.1, pp. 91–92: arithmetic and absolute-value closure
    for the summable-function lattice, from 2.4.4(3)–(4), (8), pp. 82–83.
    These supporting statements keep total finite values and arbitrary
    ambient measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic PartialExtendedArithmetic PartialAbsolutePartsGraph
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAddition MeasureIntegralAbsolute
  MeasureFiniteRealSumIntegral MeasureFiniteRealScaleIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_integral_add]: additive integral law cited in
    Federer 2.5.1, p. 92, from 2.4.4(4), p. 82 *)
Lemma real_total_integral_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (a b : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  is_measure_integral mu (real_total_integrand (fun x => (f x+g x)%R)) (a+b)%R%:E.
Proof.
move=> hf hg.
have hd : extended_add a%:E b%:E=Some (a+b)%R%:E by rewrite /extended_add /=.
have hi := @measure_integral_add R X mu hm _ _ a%:E b%:E _ hf hg hd.
exact: measure_integral_graph_equivalent (real_total_sum_embedding_graph f g) hi.
Qed.

(** Source for [real_total_integral_scale]: homogeneity cited in Federer
    2.5.1, p. 92, from 2.4.4(3), p. 82 All real coefficients, including
    zero, are valid here. *)
Lemma real_total_integral_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (a c : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x => (c * f x)%R)) (c * a)%R%:E.
Proof. exact: (@measure_finite_real_total_scale_integral R X mu hm f a c). Qed.

(** Source for [summable_real_add]: addition closure in the summable lattice
    of Federer 2.5.1, p. 91 *)
Lemma summable_real_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  summable_real_functions mu f -> summable_real_functions mu g ->
  summable_real_functions mu (fun x => (f x+g x)%R).
Proof.
move=> [a ha] [b hb]; exists (a+b)%R; exact: (@real_total_integral_add R X mu hm f g a b ha hb).
Qed.

(** Source for [summable_real_scale]: scalar closure in the summable lattice
    of Federer 2.5.1, p. 91 This example is closed under arbitrary real
    scaling, stronger than the lattice requirement. *)
Lemma summable_real_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (c : R) :
  summable_real_functions mu f -> summable_real_functions mu (fun x => (c * f x)%R).
Proof. move=> [a ha]; exists (c * a)%R; exact: (@real_total_integral_scale R X mu hm f a c ha). Qed.

(** Source for [summable_real_subtract]: ordered-difference closure in the
    summable lattice of Federer 2.5.1, p. 91 Summability gives arbitrary
    differences, so no pointwise order premise is needed for this example. *)
Lemma summable_real_subtract (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  summable_real_functions mu f -> summable_real_functions mu g ->
  summable_real_functions mu (fun x => (f x-g x)%R).
Proof.
move=> hf hg; have hn := @summable_real_scale R X mu hm g (-1)%R hg.
have hh := @summable_real_add R X mu hm f _ hf hn.
have he : (fun x => (f x+ -1 * g x)%R)=(fun x => (f x-g x)%R).
  by apply: funext=> x; rewrite mulN1r.
by rewrite he in hh.
Qed.

(** Source for [summable_real_absolute]: supporting absolute closure for the
    lattice example in Federer 2.5.1, p. 91, from 2.4.4(8), p. 82 *)
Lemma summable_real_absolute (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) :
  summable_real_functions mu f -> summable_real_functions mu (fun x => `|f x|%R).
Proof.
move=> hf; have [a ha] := @measure_summable_absolute_value R X mu hm (real_total_integrand f) hf.
exists a; apply: (@measure_integral_graph_equivalent R X mu _ _ a%:E _ ha)=> x y; split.
- move=> [z [hz he]]; have hz' := (real_total_integrand_graph f x z).1 hz.
  apply/real_total_integrand_graph; by rewrite -he -hz' abse_EFin.
- move/real_total_integrand_graph=> he; exists (f x)%:E; split.
  + by apply/real_total_integrand_graph.
  + by rewrite abse_EFin.
Qed.

(** Source for [summable_real_minimum]: binary infimum closure in the
    summable lattice of Federer 2.5.1, p. 91 The elementary identity
    min(f,g)=(f+g-|f-g|)/2 reduces it to integral arithmetic. *)
Lemma summable_real_minimum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) :
  summable_real_functions mu f -> summable_real_functions mu g ->
  summable_real_functions mu (fun x => Order.min (f x) (g x)).
Proof.
move=> hf hg.
have hs := @summable_real_add R X mu hm f g hf hg.
have hd := @summable_real_subtract R X mu hm f g hf hg.
have hab := @summable_real_absolute R X mu hm _ hd.
have hu := @summable_real_subtract R X mu hm _ _ hs hab.
have hh := @summable_real_scale R X mu hm _ (2^-1)%R hu.
have he : (fun x => (2^-1 * (f x+g x-`|f x-g x|))%R)=(fun x => Order.min (f x) (g x)).
  by apply: funext=> x; rewrite minr_absE mulrC.
by rewrite he in hh.
Qed.

(** Source for [real_total_integral_subtract]: supporting difference
    identity for the summable-function lattice in Federer 2.5.1, pp. 91–92,
    from 2.4.4(3)–(4), p. 82 *)
Lemma real_total_integral_subtract (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (a b : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  is_measure_integral mu (real_total_integrand (fun x => (f x-g x)%R)) (a-b)%R%:E.
Proof.
move=> hf hg; have hn := @real_total_integral_scale R X mu hm g b (-1)%R hg.
have hh := @real_total_integral_add R X mu hm f _ a (-1*b)%R hf hn.
have he : (fun x => (f x+ -1 * g x)%R)=(fun x => (f x-g x)%R).
  by apply: funext=> x; rewrite mulN1r.
by rewrite he mulN1r in hh.
Qed.
