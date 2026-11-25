(** Federer (1969), 2.5.3, proof p. 95: transfer from a positive simple
    approximation s to the summable target u. This supporting estimate
    retains partial domains and derives the error from a simple minorant:
    integral |h-u| is at most integral |h-s| + integral u - integral s.
    Summability gives finite values on a conull set before real arithmetic
    is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialExtendedArithmetic
  PartialAbsolutePartsGraph PartialExtendedOrderLoci SummableRealFunctionUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAddition
  MeasureIntegralDifference MeasureIntegralComparison MeasureSummableFiniteValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_subtract_finite_graph]: supporting graph adapter for
    the finite-error arithmetic in Federer 2.5.3, p. 95 This lemma is only
    used on the conull finite-value region. *)
Lemma partial_subtract_finite_graph (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) x (a b : R) :
  partial_function_graph f x a%:E -> partial_function_graph g x b%:E ->
  partial_function_graph (partial_extended_function_subtract f g) x (a-b)%R%:E.
Proof.
move=> hf hg; apply/partial_extended_function_add_graph.
exists a%:E,(-b%:E); split=> //; split.
- by exists b%:E; split.
- by rewrite /extended_add /=.
Qed.

(** Source for [partial_simple_integral_error_transfer]: supporting final
    approximation estimate for Federer 2.5.3, proof p. 95 The target f may
    be partial and extended valued on an exceptional null set; the
    almost-everywhere minorant condition includes definedness. *)
Theorem partial_simple_integral_error_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (h s : X -> R) (a b e : R) :
  is_measure_integral mu f a%:E ->
  is_measure_integral mu (real_total_integrand s) b%:E ->
  summable_real_functions mu h ->
  is_measure_integral mu (real_total_integrand (fun x => `|h x-s x|%R)) e%:E ->
  measure_almost_everywhere mu (partial_extended_le_locus (real_total_integrand s) f) ->
  exists q : R, is_measure_integral mu
    (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f)) q%:E /\
    (q <= e+(a-b))%R.
Proof.
move=> hf hs hh he hord.
have hfs : is_measure_summable mu f by exists a.
have hdiff := @measure_integral_finite_difference R X mu hm f (real_total_integrand s) a b hf hs.
have hadd : extended_add e%:E (a-b)%R%:E=Some (e+(a-b))%R%:E by rewrite /extended_add /=.
have hsum := @measure_integral_add R X mu hm _ _ e%:E (a-b)%R%:E _ he hdiff hadd.
have [_ [q hq]] := @measure_summable_difference R X mu hm (real_total_integrand h) f hh hfs.
have hfin := @measure_summable_finite_almost R X mu hm f hfs.
have hgood := @measure_almost_everywhere_and R X mu hm _ _ hfin hord.
have hbound : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f))
    (partial_extended_function_add (real_total_integrand (fun x => `|h x-s x|%R))
      (partial_extended_function_subtract f (real_total_integrand s)))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hgood).
  move=> x [[z [hz hzfin]] [r [v [hr [hv hrv]]]]].
  have hzv : z=v := partial_function_single_valued hz hv.
  have hrs := (real_total_integrand_graph s x r).1 hr.
  have hst : (s x <= fine z)%R by move: hrv; rewrite -hzv -(fineK hzfin) -hrs lee_fin.
  have hzt : partial_function_graph f x (fine z)%:E by rewrite fineK.
  have hht : partial_function_graph (real_total_integrand h) x (h x)%:E by apply/real_total_integrand_graph.
  have hstg : partial_function_graph (real_total_integrand s) x (s x)%:E by apply/real_total_integrand_graph.
  exists `|h x-fine z|%R%:E,(`|h x-s x|+(fine z-s x))%R%:E; split.
  - exists (h x-fine z)%R%:E; split; last by rewrite abse_EFin.
    exact: (@partial_subtract_finite_graph R X _ _ x (h x) (fine z) hht hzt).
  - split.
    + apply/partial_extended_function_add_graph.
      exists `|h x-s x|%R%:E,(fine z-s x)%R%:E; split; first by apply/real_total_integrand_graph.
      split; last by rewrite /extended_add /=.
      exact: (@partial_subtract_finite_graph R X _ _ x (fine z) (s x) hzt hstg).
    + rewrite lee_fin.
      have hvv : (h x-fine z)%R=((h x-s x)+(s x-fine z))%R by rewrite addrA subrK.
      have hn : `|s x-fine z|%R=(fine z-s x)%R by rewrite ler0_norm ?subr_le0 // opprB.
      rewrite hvv -hn; exact: ler_normD.
exists q; split=> //.
have hle := @measure_integral_monotone R X mu hm _ _ q%:E (e+(a-b))%R%:E hq hsum hbound.
by move: hle; rewrite lee_fin.
Qed.
