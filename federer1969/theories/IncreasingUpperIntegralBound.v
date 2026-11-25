(** Federer (1969), 2.10.25, pp. 188–189, final passage from cutoff fibre
    masses to the final Hausdorff fibre mass: supporting continuity from
    below for upper integrals of nonnegative inputs, without assuming those
    inputs measurable. Choose nonnegative measurable upper approximants
    using 2.4.2, p. 81, and apply Fatou 2.4.6, p. 84, to their lower limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitExtremaUP PartialFunctionLowerLimitSealed
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasurableFunctionUP
  MeasureIntegralUniqueness MeasureUpperIntegralMonotone MeasureNonnegativeUpperApproximation MeasureFatou
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_upper_integral_increasing_bound]: supporting
    increasing-limit upper-integral argument for the last
    line of the proof of 2.10.25, p. 189. Pointwise
    supremum is specified by its abstract laws. The
    original inputs may be nonmeasurable and infinite;
    only their upper integrals have a common finite
    real bound. No completed-sigma-algebra identification
    or integrand measurability is assumed. *)
Theorem nonnegative_upper_integral_increasing_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : nat -> X -> extended_real_line R) (f : X -> extended_real_line R) (B : R) :
  (forall n x, 0<=F n x) ->
  (forall n m, (n<=m)%N -> forall x, F n x<=F m x) ->
  (forall x, is_extended_real_supremum ((fun n=>F n x) @` setT) (f x)) ->
  (forall n, measure_upper_integral mu (partial_function_total (F n))<=B%:E) ->
  measure_upper_integral mu (partial_function_total f)<=B%:E.
Proof.
move=> hF0 hinc hsup hbound.
apply: (@extended_upper_bound_from_scaled_errors R (measure_upper_integral mu (partial_function_total f))
  B 1%R (@ler01 R))=> e he; rewrite mul1r.
have hpos n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total (F n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=> x _; exists (F n x); split=> //; exact: hF0.
have hfin n : measure_upper_integral mu (partial_function_total (F n))< +oo.
  exact: le_lt_trans (hbound n) (ltry B).
have hex n := @measure_nonnegative_upper_approximation R X mu hm
  (partial_function_total (F n)) e (hpos n) (hfin n) he.
pose V n := projT1 (cid (hex n)).
pose a n := projT1 (cid (projT2 (cid (hex n)))).
have hVa n := projT2 (cid (projT2 (cid (hex n)))).
have hVpos n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (V n)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (measurable_function_domain (hVa n).2.1.1))=> x [y hy].
  exists y; split=> //; exact: (hVa n).1 x y hy.
pose g := @PartialFunctionLowerLimit.value R X V.
have hg := @PartialFunctionLowerLimit.laws R X V.
have hgi := (@measure_fatou R X mu hm V g hg (fun n=>(hVa n).2.1.1) hVpos).1.
have hfatou := @measure_fatou_integral_values R X mu hm V g (fun n=>(a n)%:E)
  (measure_lower_integral mu g) hg hVpos (fun n=>(hVa n).2.1) hgi.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n=>partial_extended_le_locus (partial_function_total (F n)) (V n)) (countableP _)
  (fun n _=>(hVa n).2.2.1).
have hfg : measure_almost_everywhere mu (partial_extended_le_locus (partial_function_total f) g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hall)=> x hx.
  have hdom : partial_function_domain g x.
    rewrite (partial_function_lower_limit_domain hg); exists 0%N=> n hn.
    have [z [w [hz [hw hzw]]]] := hx n Logic.I; by exists w.
  have [z hz] := hdom; exists (f x),z; split=> //; split=> //.
  apply: (extended_real_supremum_least (hsup x))=> w [i _ <-].
  apply: (partial_function_lower_limit_upper hg hz).
  exists i=> n hin y hny.
  have [r [s [hr [hs hrs]]]] := hx n Logic.I.
  have heq := partial_function_single_valued hs hny.
  have hrF : F n x=r := hr.
  apply: le_trans (hinc i n hin x) _; by rewrite -hrF heq in hrs.
have hupper := @measure_upper_integral_monotone R X mu hm (partial_function_total f) g hfg.
have heq := @measure_upper_integral_unique R X mu g _ _
  (measure_upper_integral_specification mu g) hgi.2.1.
rewrite heq in hupper; apply: le_trans hupper (le_trans hfatou _).
have ha n : (a n)%:E<=(B+e)%R%:E.
  apply: le_trans (ltW (hVa n).2.2.2) _; rewrite EFinD.
  exact: leeD (hbound n) (lexx _).
apply: (extended_real_supremum_least (extended_lower_limit_laws (fun n=>(a n)%:E)))=> b [N hN].
exact: le_trans (hN N (leqnn N)) (ha N).
Qed.
