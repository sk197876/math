(** Federer (1969), 2.5.9, p. 100: almost uniqueness on a countably
    measurable ambient space. The third further condition of 2.5.3, p. 94,
    supplies a countable family of positive lattice tests whose series
    dominates one. Combining their individual conull zero-product sets
    identifies the density globally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP
  MeasurableFunctionUP FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureIntegralUP SummableRealFunctionUP TotalScalarLpUP LatticeSeriesCoverUP RegularDaniellConsequences
  NonnegativeSum NonnegativeSumSupport LatticeZeroPairingProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_lattice_zero_pairing_almost_zero]:
    supporting global conclusion for almost uniqueness in Federer
    2.5.9, p. 100. The weight is only measurable;
    no essential bound on it is required. *)
Theorem regular_lattice_zero_pairing_almost_zero (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (w : X -> R) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  measure_countably_measurable mu setT ->
  is_measure_measurable_function mu (total_scalar_function w) ->
  (forall h, L h -> is_measure_integral mu (real_total_integrand (fun x => (h x*w x)%R)) 0) ->
  measure_almost_everywhere mu [set x | w x=0%R].
Proof.
move=> hrep hr hX hw hz.
have hfinite : is_countably_finite_measure_set mu setT.
  have [C [hC [he hfin]]] := hX.
  exists C; split=> //; split; first by move=> B hB; exact: (hfin B hB).2.
  by rewrite -he.
have [f hf] := (proj1 (@regular_daniell_countably_finite_iff R X L F hL mu hm hrep hr setT)) hfinite.
have hprod n := @lattice_zero_pairing_product_almost_zero R X L hL F mu hm w hrep hr hw hz (f n) (hf.1 n).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => [set x | (f n x*w x)%R=0%R]) (countableP setT) (fun n _ => hprod n).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx.
case: (eqVneq (w x) 0%R)=> // hneq.
have hfn n : f n x=0%R.
  have he : (f n x*w x)%R=0%R := hx n I.
  move/eqP: he; rewrite mulf_eq0 (negbTE hneq) orbF; exact/eqP.
have hsum : nonnegative_sum setT (fun n : nat => (f n x)%:E)=0.
  apply: nonnegative_sum_zero=> n _; by rewrite hfn.
have hh := hf.2 x I; by rewrite hsum lee_fin ler10 in hh.
Qed.
