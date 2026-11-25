(** Federer (1969), 2.6.4, pp. 118–119: density follows by finite-simple
    approximation and signed decomposition, citing 2.4.4(6), p. 82. We prove
    the supporting criterion for any linear subspace of summable functions
    whose closure contains finite-measure characteristic functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence PartialExtendedOrderLoci
  SummableRealFunctionUP SummableRealArithmetic CharacteristicFunctionUP TotalAbsoluteDifferenceGraph
  SubspaceLoneApproximationUP SubspaceLoneApproximationArithmetic SubspacePositiveDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Density.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Variable L : subspace (GRing.Lmodule.clone R (X -> R^o) _).
Hypothesis hLs : forall f, L f -> summable_real_functions mu f.
Hypothesis hchar : forall (A : set X) (s : X -> R), measure_measurable mu A ->
  (mu A < +oo)%E -> is_characteristic_function A s -> is_subspace_lone_approximable mu L s.

(** Source for [subspace_nonnegative_total_density]: total-domain
    form of the nonnegative reduction in Federer 2.6.4,
    pp. 118–119, respecting erratum p. 2, book p. 119
    lines 3, 4, 6. *)
Lemma subspace_nonnegative_total_density f : summable_real_functions mu f ->
  (forall x, 0<=f x) -> is_subspace_lone_approximable mu L f.
Proof.
move=> hf hf0; split=> // d hd.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand f)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin; exact: hf0.
have [h [q [hh [hi hq]]]] := @subspace_nonnegative_summable_density R X mu hm L hLs hchar
  (real_total_integrand f) d hf hp hd.
exists h,q; split=> //; split=> //.
exact (@measure_integral_graph_equivalent R X mu _ _ _ (total_absolute_difference_graph h f) hi).
Qed.

(** Source for [subspace_summable_total_density]: the signed
    reduction completing the density argument in Federer 2.6.4,
    p. 119. We use f=(f+|f|)-|f|, so both
    nonnegative terms are summable without additional hypotheses. *)
Theorem subspace_summable_total_density f : summable_real_functions mu f ->
  is_subspace_lone_approximable mu L f.
Proof.
move=> hf; have hab := @summable_real_absolute R X mu hm f hf.
have hsum := @summable_real_add R X mu hm f _ hf hab.
have habdense := @subspace_nonnegative_total_density _ hab (fun x => normr_ge0 (f x)).
have hpos x : 0<=f x+`|f x|.
  have hh := ler_norm (-f x); rewrite normrN in hh.
  move: hh; by rewrite -subr_ge0 opprK addrC.
have hsumdense := @subspace_nonnegative_total_density _ hsum hpos.
have hneg := @subspace_lone_approximable_negate R X mu hm L (fun x => `|f x|) habdense.
have hd := @subspace_lone_approximable_add R X mu hm L hLs _ _ hsumdense hneg.
have he : (fun x => f x+`|f x|+ -`|f x|)=f by apply: funext=> x; rewrite addrK.
by rewrite he in hd.
Qed.
End Density.
