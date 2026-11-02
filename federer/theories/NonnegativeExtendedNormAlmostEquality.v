(** Supporting null-modification invariance for Federer (1969), 2.10.5, p.
    173, exponent comparison and common null sets. Use the equality
    convention of 2.3.1, p. 72, and the actual norm formulas of 2.4.12, p.
    86. Finite exponents use the proved integral null-modification law;
    infinity uses null superlevels and the exceptional null set. Infinite
    values may be changed only on a proved null set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower PartialFunctionUP
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralAlmostEquality NonnegativeExtendedExponentNormUP NonnegativeExtendedExponentNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_null_thresholds_almost_equal]:
    supporting null-superlevel invariance for the
    infinity-exponent comparisons in Federer
    2.10.5, p. 173. Equal inputs off a
    null exceptional set have the same admissible
    essential bounds from 2.4.12, p. 86. *)
Lemma extended_null_thresholds_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) (r : \bar R) :
  measure_almost_everywhere mu [set x | f x=g x] ->
  (nonnegative_extended_essential_thresholds mu f r <->
   nonnegative_extended_essential_thresholds mu g r).
Proof.
move=> he.
have hdir (u v : X -> extended_real_line R) :
    measure_almost_everywhere mu [set x | u x=v x] ->
    nonnegative_extended_essential_thresholds mu u r ->
    nonnegative_extended_essential_thresholds mu v r.
  move=> hae [hr hz]; split=> //.
  have hnull := @measure_null_union R X mu hm [set x | r<u x]
    (~` [set x | u x=v x]) hz hae.
  apply: (@measure_null_subset R X mu hm _ _ _ hnull)=> x hx.
  case: (pselect (u x=v x))=> [h|h].
  - left; change (is_true (r<u x)); by rewrite h.
  - by right.
split; first exact: hdir he.
apply: hdir; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
exact: esym hx.
Qed.

(** Source for [nonnegative_extended_norm_specification_almost_equal]:
    supporting transport of the norm formulas
    used in Federer 2.10.5, p. 173, under
    the equality convention of 2.3.1, p. 72.
    No infinite input is discarded without the
    explicit almost-equality hypothesis. *)
Lemma nonnegative_extended_norm_specification_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) (t a : \bar R) :
  measure_almost_everywhere mu [set x | f x=g x] ->
  is_nonnegative_extended_exponent_norm mu f t a ->
  is_nonnegative_extended_exponent_norm mu g t a.
Proof.
move=> he; case: t=> [p| |] //=.
- move=> [hp [b [hi ha]]]; split=> //; exists b; split=> //.
  apply: (measure_integral_almost_equal hm hi _).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x hx.
  exists (extended_positive_power (f x) p); split=> //; by rewrite hx.
- move=> hn; split.
  - move=> r hr; apply: hn.1.
    exact: (@extended_null_thresholds_almost_equal R X mu hm f g r he).2 hr.
  - move=> b hb; apply: hn.2=> r hr; apply: hb.
    exact: (@extended_null_thresholds_almost_equal R X mu hm f g r he).1 hr.
Qed.

(** Source for [nonnegative_extended_norm_almost_equal]:
    supporting invariance of the actual sealed
    norm numerator in Federer 2.10.5, p. 173,
    on nonnegative measurable inputs equal almost
    everywhere. All exponents t>=1 are covered. *)
Theorem nonnegative_extended_norm_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) (t : \bar R) :
  (forall x, 0<=f x) -> (forall x, 0<=g x) -> 1<=t ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_almost_everywhere mu [set x | f x=g x] ->
  nonnegative_extended_exponent_norm mu f t=nonnegative_extended_exponent_norm mu g t.
Proof.
move=> hf0 hg0 ht hf hg he.
have hs := @nonnegative_extended_exponent_norm_specification R X mu f t hm hf0 ht hf.
have hs' := @nonnegative_extended_norm_specification_almost_equal R X mu hm f g t _ he hs.
exact: nonnegative_extended_exponent_norm_unique hs'
  (@nonnegative_extended_exponent_norm_specification R X mu g t hm hg0 ht hg).
Qed.
