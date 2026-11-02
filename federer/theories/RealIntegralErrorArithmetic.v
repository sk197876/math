(** Federer (1969), 2.5.3, proof p. 95: passing approximation from
    characteristic functions to finite positive combinations. The needed
    integral arithmetic is 2.4.4(3)–(5), pp. 82–83. These supporting lemmas
    concern finite total real functions and finite integral errors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MeasureUP MeasureIntegralUP MeasureIntegralComparison
  SummableRealFunctionUP SummableRealArithmetic RealTotalCharacteristicBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_total_integral_error_scale]: homogeneity of the
    absolute error in the finite-combination step of Federer 2.5.3, p. 95 *)
Lemma real_total_integral_error_scale (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : X -> R) (a c : R) :
  (0 <= c)%R -> is_measure_integral mu (real_total_integrand (fun x => `|f x-g x|%R)) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x => `|c*f x-c*g x|%R)) (c*a)%R%:E.
Proof.
move=> hc hi; have hh := @real_total_integral_scale R X mu hm _ a c hi.
have he : (fun x => (c*`|f x-g x|)%R)=(fun x => `|c*f x-c*g x|%R).
  by apply: funext=> x; rewrite -mulrBr normrM ger0_norm.
by rewrite he in hh.
Qed.

(** Source for [real_total_integral_error_add]: subadditivity of the
    absolute error in the finite-combination step of Federer 2.5.3, p. 95
    The actual integral of the combined error is supplied, rather than only
    a bound on an unspecified upper integral. *)
Lemma real_total_integral_error_add (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g u v : X -> R) (a b : R) :
  summable_real_functions mu f -> summable_real_functions mu g ->
  summable_real_functions mu u -> summable_real_functions mu v ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x-g x|%R)) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x => `|u x-v x|%R)) b%:E ->
  exists e : R, is_measure_integral mu
    (real_total_integrand (fun x => `|(f x+u x)-(g x+v x)|%R)) e%:E /\ (e <= a+b)%R.
Proof.
move=> hf hg hu hv ha hb.
have hfu := @summable_real_add R X mu hm f u hf hu.
have hgv := @summable_real_add R X mu hm g v hg hv.
have hsub := @summable_real_subtract R X mu hm _ _ hfu hgv.
have [e he] := @summable_real_absolute R X mu hm _ hsub.
have hsum := @real_total_integral_add R X mu hm _ _ a b ha hb.
exists e; split=> //.
have hle : function_le (fun x => `|(f x+u x)-(g x+v x)|%R)
    (fun x => (`|f x-g x|+`|u x-v x|)%R).
  move=> x; rewrite opprD addrACA; exact: ler_normD.
have hh := @measure_integral_monotone R X mu hm _ _ e%:E (a+b)%R%:E he hsum
  (@real_total_pointwise_order_almost R X mu hm _ _ hle).
by move: hh; rewrite lee_fin.
Qed.
