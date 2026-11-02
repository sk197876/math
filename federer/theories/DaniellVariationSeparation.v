(** Federer (1969), 2.5.5, pp. 96–97: the final lower-limit separation
    assertion, proved by the two L1 error estimates, convergence in measure,
    and two applications of 2.3.10. The lower limit is finite on every point
    of X, including the two exceptional sets; it is not assumed to belong to
    L. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ScalarNormMetricCompleteness PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP FunctionLatticeUP FunctionLatticeLaws DaniellIntegralUP DaniellVariationUP
  DaniellVariationIntegralErrors SummableRealFunctionUP RealIntegralFunctionalUP SummableRealNormed
  MeasureScalarL1Convergence MeasureConvergentSubsequence BoundedRealFunctionLowerLimit
  ExtendedLowerLimitUP ExtendedConvergentLowerLimit MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureConvergenceUP MeasurableNormedFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_variation_separating_lower_limit]: exact postscript
    of Federer 2.5.5, p. 96, proof p. 97 A single sequence k_n in L+ below f
    gives a globally finite h=liminf k_n, equal to f almost everywhere for
    the positive measure and zero almost everywhere for the negative
    measure. Regularity is not needed once the two integral representations
    are supplied. *)
Theorem daniell_variation_separating_lower_limit (R : realType) (X : choiceType)
    (L : set (X -> R)) (A P Q : (X -> R) -> R)
    (hL : is_function_lattice L) (hA : is_daniell_integral L A)
    (hP : is_daniell_positive_variation L A P) (hQ : is_daniell_negative_variation L A Q)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hmu : is_real_integral_functional mu (positive_function_lattice L) P)
    (hnu : is_real_integral_functional nu (positive_function_lattice L) Q) (f : X -> R) :
  positive_function_lattice L f -> exists (k : nat -> X -> R) (h : X -> R),
    (forall n, lattice_positive_order_interval L f (k n)) /\
    (forall x, (0 <= h x <= f x)%R) /\
    (forall x, is_extended_lower_limit (fun n => (k n x)%:E) (h x)%:E) /\
    measure_almost_everywhere mu [set x | h x=f x] /\
    measure_almost_everywhere nu [set x | h x=0%R].
Proof.
move=> hf.
have [g [hg [hplus hminus]]] := @daniell_variation_two_error_limits R X L A P Q hL hA hP hQ f hf.
pose M := real_norm_metric_space (scalar_absolute_value_norm R).
pose G n := partial_function_total (g n : X -> M).
pose F := partial_function_total (f : X -> M).
pose Z := partial_function_total (fun _ : X => (0%R : M)).
have hGmu n : @is_measurable_normed_function R X R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) mu (G n).
  apply: (@summable_real_function_in_normed_collection R X mu hm (g n)).
  exists (P (g n)); exact: hmu (g n) (conj (hg n).1 (hg n).2.1).
have hGnu n : @is_measurable_normed_function R X R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) nu (G n).
  apply: (@summable_real_function_in_normed_collection R X nu hn (g n)).
  exists (Q (g n)); exact: hnu (g n) (conj (hg n).1 (hg n).2.1).
have hF : @is_measurable_normed_function R X R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) mu F.
  apply: (@summable_real_function_in_normed_collection R X mu hm f).
  exists (P f); exact: hmu f hf.
have hzero : positive_function_lattice L (fun _ => 0%R).
  split; first exact: (@function_lattice_zero R X L hL f hf.1).
  by move=> x; exact: lexx.
have hZ : @is_measurable_normed_function R X R^o (fun x : R => `|x|%R) (scalar_absolute_value_norm R) nu Z.
  apply: (@summable_real_function_in_normed_collection R X nu hn (fun _ => 0%R)).
  exists (Q (fun _ => 0%R)); exact: hnu _ hzero.
have hcmu : converges_in_measure mu (fun x : R^o => `|x|%R) G F.
  apply: (@real_total_l1_converges_in_measure R X mu hm g f (fun n => (P f-P (g n))%R) _ hplus)=> n.
  exact: (@daniell_variation_positive_error_integral R X L P mu hm hmu f (g n) hf (hg n)).
have hcnu : converges_in_measure nu (fun x : R^o => `|x|%R) G Z.
  apply: (@real_total_l1_converges_in_measure R X nu hn g (fun _ => 0%R) (fun n => Q (g n)) _ hminus)=> n.
  have he : (fun x => `|g n x-0|%R)=(fun x => `|g n x|%R) by apply: funext=> x; rewrite subr0.
  rewrite he; exact: (@daniell_variation_negative_error_integral R X L Q nu hnu f (g n) (hg n)).
have [s [t [hs [ht [hamu hanu]]]]] := @two_measures_common_almost_subsequence R X R^o
  (fun x : R => `|x|%R) (scalar_absolute_value_norm R) (@scalar_norm_metric_complete R)
  mu nu hm hn G F Z hGmu hF hGnu hZ hcmu hcnu.
pose k n := g (s (t n)).
have hk n : lattice_positive_order_interval L f (k n) := hg (s (t n)).
have hb n x : (0 <= k n x <= f x)%R by apply/andP; split; [exact: (hk n).2.1|exact: (hk n).2.2].
have [h [hh hl]] := @bounded_real_function_lower_limit_exists R X k f hb.
exists k,h; split; first exact: hk.
split; first exact: hh.
split; first exact: hl.
split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hamu)=> x hx.
  have hc := @total_scalar_limit_locus_order_limit R X k f x hx.
  have he := extended_lower_limit_unique (hl x) (extended_convergent_lower_limit hc).
  by injection he.
- apply: (@measure_almost_everywhere_mono R X nu hn _ _ _ hanu)=> x hx.
  have hc := @total_scalar_limit_locus_order_limit R X k (fun _ => 0%R) x hx.
  have he := extended_lower_limit_unique (hl x) (extended_convergent_lower_limit hc).
  by injection he.
Qed.
