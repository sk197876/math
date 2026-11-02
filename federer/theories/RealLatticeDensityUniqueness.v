(** Federer (1969), 2.5.9, p. 100: almost uniqueness among all measurable
    representing densities. The proof uses the corrected positive-density
    step, erratum p. 2, book p. 100 line 22, localized dominated
    convergence, and a countable positive-lattice series cover. No essential
    bound is assumed on either competing density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From mathcomp.analysis.normedtype_theory Require Import pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP MeasurableFunctionUP FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureIntegralUP SummableRealFunctionUP SummableRealArithmetic TotalScalarLpUP TotalScalarMeasurability
  RealLatticeDensityUP RegularLatticeZeroPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_lattice_density_almost_unique]: complete
    almost-uniqueness assertion in Federer 2.5.9, p. 100.
    The hypotheses on the comparison density are measurability and
    the actual finite integral formula on L, without a norm bound. *)
Theorem real_lattice_density_almost_unique (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F A : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) (k l : X -> R) :
  is_real_integral_functional mu L F -> is_function_lattice_regular L mu ->
  measure_countably_measurable mu setT ->
  is_real_lattice_density mu L A k -> is_real_lattice_density mu L A l ->
  measure_almost_everywhere mu [set x | k x=l x].
Proof.
move=> hrep hr hX hk hl.
pose w x := (k x-l x)%R.
have hw : is_measure_measurable_function mu (total_scalar_function w).
  apply: (@total_scalar_continuous_binary_operation R X mu hm k l (fun p => (p.1-p.2)%R) _ hk.1 hl.1).
  change (continuous (fun p : R^o * R^o => (p.1-p.2)%R)).
  move=> p; apply: cvgB; [exact: cvg_fst|exact: cvg_snd].
have hz f : L f -> is_measure_integral mu (real_total_integrand (fun x => (f x * w x)%R)) 0.
  move=> hf.
  have hi := @real_total_integral_subtract R X mu hm
    (fun x => (f x * k x)%R) (fun x => (f x * l x)%R) (A f) (A f) (hk.2 f hf) (hl.2 f hf).
  rewrite subrr in hi.
  have he : (fun x => (f x * k x-f x * l x)%R)=(fun x => (f x * w x)%R).
    by apply: funext=> x; rewrite /w mulrBr.
  by rewrite he in hi.
have ha := @regular_lattice_zero_pairing_almost_zero R X L hL F mu hm w hrep hr hX hw hz.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ ha)=> x hx.
change (k x=l x); apply/eqP; rewrite -subr_eq0; apply/eqP; exact: hx.
Qed.
