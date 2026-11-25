(** Federer (1969), 2.10.36, printed p. 198: the two-apex volume comparison
    uses the normalised section profile (1-|t|)^n on [-1,1]. Its integral is
    2/(n+1). Combine the two already proved half-profile integrals,
    identifying their zero extensions outside the common endpoint. The
    endpoint has scalar Lebesgue measure zero. Source context and calculus
    background: BipyramidPowerIntegral.v. These are supporting calculations
    for the printed volume estimate, not additional numbered assertions of
    the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure PowerSegmentIntegral BipyramidPowerIntegral
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureSubsetIntegral MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP SummableRealArithmetic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_segment_zero_extension_integral]: supporting
    graph adapter for the section-profile
    integral in 2.10.36, p. 198.
    It merely writes the specified zero
    extension of a segment-restricted real
    input as an if-then-else total function. *)
Lemma real_segment_zero_extension_integral (R : realType) (mu : set R -> \bar R)
    (a b : R) (f : R -> R) (r : \bar R) :
  is_measure_subset_integral mu `[a,b] (real_total_integrand f) r ->
  is_measure_integral mu (real_total_integrand
    (fun t=>if a<=t<=b then f t else 0)) r.
Proof.
move=> hi; apply: (measure_integral_graph_equivalent _ hi)=> t z.
rewrite partial_function_zero_extension_graph real_total_integrand_graph /= in_itv /=.
rewrite ?real_total_integrand_graph.
case: ifP=> h; split.
- by move=> [[_ <-]|[hn _]]; [exists (f t)|].
- by move=> [y [<- <-]]; left.
- by move=> [[hn _]|[_ ->]]; [|exists 0].
- by move=> [y [<- <-]]; right.
Qed.

(** Source for [bipyramid_hat_profile_integral]: supporting
    integral of the normalised two-apex
    cross-section profile in 2.10.36, p. 198.
    Its value is 2/(n+1), including
    n=0, where the profile is the
    characteristic function of [-1,1]. *)
Theorem bipyramid_hat_profile_integral (R : realType) (n : nat) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun t : R=>if `|t|<=1 then (1-`|t|)^+n else 0))
    (2*n.+1%:R^-1)%R%:E.
Proof.
pose fp (t : R) := if 0<=t<=1 then (1-t)^+n else 0.
pose fm (t : R) := if -1<=t<=0 then (1+t)^+n else 0.
pose f (t : R) := if `|t|<=1 then (1-`|t|)^+n else 0.
have hp : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand fp) (n.+1%:R^-1)%:E.
  exact: real_segment_zero_extension_integral (complement_power_segment_integral R n).
have hm : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand fm) (n.+1%:R^-1)%:E.
  exact: real_segment_zero_extension_integral (reflected_complement_power_segment_integral R n).
have hs := real_total_integral_add (lebesgue_scalar_is_measure R) hp hm.
have hval : n.+1%:R^-1+n.+1%:R^-1=(2 : R)*n.+1%:R^-1 by ring.
rewrite hval in hs.
have hne : measure_almost_everywhere (@lebesgue_scalar_measure R) [set t : R | t!=0].
  apply: (@measure_null_subset R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    (~` [set t : R | t!=0]) [set 0]).
  - move=> t ht; case: (eqVneq t 0)=> [->|hneq] //; exfalso; exact: ht hneq.
  - exact: lebesgue_scalar_singleton.
apply: (measure_integral_almost_equal (lebesgue_scalar_is_measure R) hs).
apply: (@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  [set t : R | t!=0] _ _ hne)=> t ht.
change (is_true (t!=0)) in ht.
have he : fp t+fm t=f t.
  case: (ltgtP t 0)=> [hneg|hpos|hz]; last by rewrite hz eqxx in ht.
  - have h0 : (0<=t)=false by rewrite leNgt hneg.
    have hle : t<=0 := ltW hneg.
    have heq : (-t<=1)=(-1<=t) by rewrite lerNl.
    by rewrite /fp /fm /f (ltr0_norm hneg) h0 hle andFb andbT add0r heq opprK.
  - have h0 : 0<=t := ltW hpos.
    have hle : (t<=0)=false by rewrite leNgt hpos.
    by rewrite /fp /fm /f (ger0_norm h0) h0 hle andTb andbF addr0.
exists (f t)%:E; split; apply/real_total_integrand_graph; first by rewrite he.
by [].
Qed.
