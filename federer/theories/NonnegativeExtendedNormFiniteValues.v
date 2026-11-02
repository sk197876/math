(** Supporting almost-everywhere finite values for the exponent comparisons
    in Federer (1969), 2.10.5, p. 173. For finite exponent, a finite norm
    gives a finite power integral; 2.4.3(4), p. 82, makes the powered input
    finite almost everywhere. For infinity, a finite strict essential bound
    excludes infinite values outside a null set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedPositivePower PartialFunctionUP
  PartialFunctionBasic PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureNonnegativeLowerIntegral
  MeasureFiniteUpperApproximant NonnegativeExtendedExponentNormUP
  NonnegativeExtendedExponentNorm NonnegativeExtendedEssentialBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_nonnegative_extended_norm_almost_finite]:
    supporting finite-value reduction for the
    probability exponent comparison used in Federer
    2.10.5, p. 173. It is proved from
    the norm formulas and 2.4.3(4), p. 82;
    finiteness is not assumed before replacing
    extended values by a scalar representative. *)
Theorem finite_nonnegative_extended_norm_almost_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (t a : \bar R) :
  (forall x, 0<=f x) -> is_nonnegative_extended_exponent_norm mu f t a -> a < +oo ->
  measure_almost_everywhere mu [set x | f x \is a fin_num].
Proof.
move=> hf0; case: t=> [p| |] //=.
- move=> [hp [b [hi ha]]] haf.
  pose H : partial_function X (extended_real_line R) :=
    partial_function_total (fun x => extended_positive_power (f x) p).
  have hp0 : (0<p)%R := lt_le_trans ltr01 hp.
  have hpi : (0<p^-1)%R by rewrite invr_gt0.
  have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus H).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _
      (measure_almost_everywhere_true hm))=> x _.
    exists (extended_positive_power (f x) p); split=> //.
    exact: extended_positive_power_nonnegative.
  have hlo := @measure_lower_integral_unique R X mu H _ b
    (measure_lower_integral_specification mu H) hi.2.2.
  have hb0 : 0<=b.
    have h := @measure_lower_integral_nonnegative R X mu hm H hpos.
    by rewrite hlo in h.
  have hbfin : b < +oo.
    by move: haf; rewrite ha (@extended_positive_power_finite_iff R b p^-1 hb0 hpi).
  have hu := @measure_upper_integral_unique R X mu H _ b
    (measure_upper_integral_specification mu H) hi.2.1.
  have hupper : measure_upper_integral mu H < +oo by rewrite hu.
  have hfinite := @finite_upper_integral_below_infinity_almost R X mu hm H hupper.
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfinite)=> x [z [hz hzfin]].
  have he : extended_positive_power (f x) p=z := hz.
  have hpowfin : extended_positive_power (f x) p < +oo by rewrite he.
  have hxfin : f x < +oo.
    by move: hpowfin; rewrite (@extended_positive_power_finite_iff R (f x) p (hf0 x) hp0).
  change (is_true (f x \is a fin_num)).
  by rewrite (ge0_fin_numE (hf0 x)).
- move=> hn haf.
  have ha0 := @nonnegative_extended_exponent_norm_nonnegative R X mu f +oo a hn.
  have hnum : a \is a fin_num by rewrite (ge0_fin_numE ha0).
  pose c := fine a.
  have ha : a=c%:E by rewrite /c fineK.
  have hstrict : a<(c+1)%R%:E by rewrite ha lte_fin ltrDl.
  have [_ hnull] := @nonnegative_extended_essential_strict_upper R X mu hm f a
    (c+1)%R%:E hn hstrict.
  apply: (@measure_null_subset R X mu hm (~` [set x | f x \is a fin_num])
    [set x | (c+1)%R%:E<f x] _ hnull)=> x hnot.
  change (is_true ((c+1)%R%:E<f x)).
  case hfx: (f x)=> [r| |].
  - exfalso; apply: hnot; change (is_true (f x \is a fin_num)).
    by rewrite hfx fin_numE.
  - exact: ltry.
  - have h := hf0 x; by rewrite hfx in h.
Qed.
