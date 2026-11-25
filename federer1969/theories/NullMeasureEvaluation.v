(** Federer (1969), 2.5.8, p. 100: necessity of the null-norm condition
    added in erratum p. 2, book p. 100 line 3. This is a counterexample to
    the uncorrected statement, not to the erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureFiniteClosure
  CountablyMeasurableUP CountablyMeasurableSubsets MeasurableFunctionUP DaniellEmptyBoundary
  MeasureEssentialNormAttainment MeasureExponentDomain TotalScalarLpUP MonotoneDaniellIntegralUP DaniellIntegralUP
  DaniellIntegralNegation MeasureIntegralUP MeasureIntegralUniqueness MeasureConullZeroIntegral
  SummableRealFunctionUP LpFunctionalDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_measure_total_linfinity]: Supporting Federer 2.5.8, p.
    100. *)
Lemma null_measure_total_linfinity (R : realType) (X : choiceType) (f : X -> R) :
  total_scalar_lp (fun _ : set X => (0 : \bar R)) +oo f.
Proof.
pose mu := fun _ : set X => (0 : \bar R).
have hm : is_measure mu := @daniell_zero_measure R X.
have hf : is_measure_measurable_function mu (total_scalar_function f).
  constructor; first by [].
  move=> U hU; exact: (@measure_null_measurable R X mu hm _ erefl).
split; first exact: leey.
split=> //; split.
- rewrite /total_scalar_lp_norm /measure_exponent_norm null_measure_essential_norm_zero.
  exact: ltry.
- constructor=> //; exact: (@null_set_countably_measurable R X mu hm _ erefl).
Qed.

(** Source for [point_evaluation_is_daniell]: Supporting counterexample to
    the uncorrected Federer 2.5.8, p. 100: evaluation at a point satisfies
    the Daniell integral laws. Erratum p. 2, book p. 100 line 3, supplies
    the necessary null-norm condition for representation. *)
Lemma point_evaluation_is_daniell (R : realType) (X : Type)
    (L : set (X -> R)) (a : X) :
  is_daniell_integral L (fun f => f a).
Proof.
apply: monotone_daniell_is_daniell; constructor.
- by [].
- by [].
- by move=> f g hf hg hfg; exact: hfg a.
- by move=> f g hf hg hfg; exact: hfg a.
Qed.

(** Source for [null_measure_evaluation_not_representable]: Supporting
    Federer 2.5.8, p. 100.The constant-one test has zero norm but evaluation
    one; all its product integrals vanish. *)
Theorem null_measure_evaluation_not_representable (R : realType) (X : choiceType) (a : X) :
  ~ exists k : X -> R, is_lp_functional_density (fun _ : set X => (0 : \bar R))
    +oo 1 (fun f => f a) k.
Proof.
move=> [k [_ hk]].
have hi := hk (fun _ => 1%R) (@null_measure_total_linfinity R X (fun _ => 1%R)).
have hz : is_measure_integral (fun _ : set X => (0 : \bar R))
    (real_total_integrand (fun x => (1*k x)%R)) 0.
  apply: (@measure_almost_zero_integral R X _ (@daniell_zero_measure R X)); by [].
have he := measure_integral_unique hi hz.
have hh : (1%R : R)=0%R := EFin_inj he.
by move: (oner_neq0 R); rewrite hh eqxx.
Qed.
