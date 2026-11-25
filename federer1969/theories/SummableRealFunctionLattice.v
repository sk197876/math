(** Federer (1969), 2.5.1, p. 91: the summable real-valued functions form a
    lattice. The nonnegative truncation ceiling need not itself be summable:
    its minimum with f is dominated in absolute value by |f|. Thus no
    finite-total-measure assumption is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialUpperTruncation
  PartialAbsolutePartsGraph PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableUpperTruncation MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAbsolute
  MeasureAbsoluteSummability FunctionLatticeUP SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_ceiling_absolute_bound]: supporting truncation
    bound for the summable lattice of Federer 2.5.1, p. 91 A negative
    ceiling would invalidate this uniform domination. *)
Lemma nonnegative_ceiling_absolute_bound (R : realType) (r c : R) :
  (0 <= c)%R -> (`|Order.min r c| <= `|r|)%R.
Proof.
move=> hc; case: (leP r c)=> h; first by [].
rewrite (ger0_norm hc).
exact: le_trans (ltW h) (ler_norm r).
Qed.

(** Source for [summable_real_truncation]: the constant-truncation clause
    for the summable lattice in Federer 2.5.1, p. 91 The source measure is
    arbitrary. *)
Lemma summable_real_truncation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> R) (c : R) :
  (0 <= c)%R -> summable_real_functions mu f ->
  summable_real_functions mu (fun x => Order.min (f x) c).
Proof.
move=> hc hf.
pose u := real_total_integrand f.
pose v := partial_upper_truncation u c%:E.
have [a ha] := hf.
have hv := @measurable_upper_truncation R X mu hm u c%:E ha.1.
have hab := @measure_summable_absolute_value R X mu hm u hf.
have hb : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value v) (partial_extended_function_absolute_value u)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|Order.min (f x) c|%R)%:E,(`|f x|%R)%:E; split.
  - exists (Order.min (f x) c)%:E; split.
    + exists (f x)%:E; split; first by apply/real_total_integrand_graph.
      by rewrite -EFin_min.
    + by rewrite abse_EFin.
  - split.
    + exists (f x)%:E; split; first by apply/real_total_integrand_graph.
      by rewrite abse_EFin.
    + rewrite lee_fin; exact: nonnegative_ceiling_absolute_bound hc.
have [b hbi] := (@measure_dominated_summable R X mu hm v _ hv hab hb).1.
exists b; apply: (@measure_integral_graph_equivalent R X mu v _ b%:E _ hbi)=> x y; split.
- move=> [z [hz he]]; have hz' := (real_total_integrand_graph f x z).1 hz.
  apply/real_total_integrand_graph; by rewrite -he -hz' -EFin_min.
- move/real_total_integrand_graph=> he; exists (f x)%:E; split.
  + by apply/real_total_integrand_graph.
  + by rewrite -EFin_min.
Qed.

(** Source for [summable_real_functions_lattice]: full summable example in
    Federer 2.5.1, p. 91 Every closure law is derived from the earlier
    integral theorems, without an external measure library. *)
Theorem summable_real_functions_lattice (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_function_lattice (summable_real_functions mu).
Proof.
constructor.
- move=> f g; exact: (@summable_real_add R X mu hm f g).
- move=> c f hc; exact: (@summable_real_scale R X mu hm f c).
- move=> f g; exact: (@summable_real_minimum R X mu hm f g).
- move=> c f hc; exact: (@summable_real_truncation R X mu hm f c hc).
- move=> f g hf hg hfg; exact: (@summable_real_subtract R X mu hm g f hg hf).
Qed.
