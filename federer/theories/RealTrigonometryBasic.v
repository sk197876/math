(** Federer (1969), 3.2.7, p. 246:
    basic regularity and actual multiplicities of the
    sine, derived only from the opaque scalar laws.
    No private trigonometric witness is imported here. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialScalar NormedCurveDerivativeUP
  NormHigherCurveDerivativeUP NormDifferentialConvexBound InnerConvex RealMetricBackground
  LipschitzUP LipschitzRealAbsoluteContinuity MetricCurveAbsoluteContinuityBasic LocallyAbsolutelyContinuousCurve
  RealTrigonometryUP RealTrigonometrySealed PeriodicMappingMultiplicity MappingMultiplicity CountingMeasure
  MeasureUP MeasureBasic FiniteCountingSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Basic.
Variable R:realType.
Local Notation S:=(@RealTrigonometry.sine R).
Local Notation C:=(@RealTrigonometry.cosine R).
Local Notation A:=(@RealTrigonometry.arcsine R).
Local Notation p:=(@RealTrigonometry.half_period R).
Local Notation ht:=(@RealTrigonometry.laws R).

(** Source for [real_sine_full_differential]: supporting
    actual sine differential for the first example in
    Federer 3.2.7, p. 246. Its coefficient is
    the opaque cosine at every source point. *)
Lemma real_sine_full_differential a:
  has_norm_differential (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) (fun _=>True) S a
    (@scalar_coefficient_linear_map R R^o (C a)).
Proof.
apply:(@norm_differential_real_source R R^o (fun t=>`|t|) (@scalar_absolute_value_norm R)
  (fun _=>True) S a _).2; split.
- exists 1; split; first exact:ltr01; by move=>h _.
- change (has_normed_curve_derivative (fun t:R^o=>`|t|) S a (1*C a)).
  rewrite mul1r scalar_normed_curve_derivative; exact (@real_sine_derivative R S C A p ht a).
Qed.

(** Source for [real_sine_nonexpanding]: the Lipschitz
    hypothesis for f=sin in the first example of
    Federer 3.2.7, p. 246. It follows from
    the actual derivative and the proved convex-domain
    differential bound, rather than an imported Lipschitz theorem. *)
Lemma real_sine_nonexpanding x y:`|S x-S y|<=`|x-y|.
Proof.
pose N:=fun t:R^o=>`|t|.
have hN:=scalar_absolute_value_norm R.
have hConvex:is_inner_convex (@setT R^o) by move=>u v _ _ t _ _.
have hD a:exists L:Hom R^o R^o,
    has_norm_differential N N (fun _=>True) S a L /\ forall t,N (L t)<= 1*N t.
  exists (@scalar_coefficient_linear_map R R^o (C a)); split; first exact:real_sine_full_differential.
  move=>t; change (`|t*C a|<= 1 * `|t|).
  rewrite normrM mul1r -[leRHS]mulr1.
  exact (ler_wpM2l (normr_ge0 t) (real_cosine_bound ht a)).
have hB:=@norm_differential_convex_bound R R^o R^o N N hN hN
  setT setT S 1 hConvex ler01 (fun a _=>hD a) x y I I.
by rewrite mul1r in hB.
Qed.

(** Source for [real_sine_locally_absolutely_continuous]:
    absolute continuity of the printed sine example
    in Federer 3.2.7, p. 246, on every
    compact scalar interval. *)
Lemma real_sine_locally_absolutely_continuous:
  is_locally_absolutely_continuous_curve (S:R->real_line_metric R).
Proof.
move=>a b hab; apply:(metric_absolute_continuity_real_agreement S a b).2.
apply:(lipschitz_real_curve_absolutely_continuous a b (@ler01 R))=>x y.
by rewrite mul1r; exact:real_sine_nonexpanding.
Qed.

(** Source for [real_sine_period]: the positive full
    period supporting infinite multiplicity in Federer
    3.2.7, p. 246, derived from two
    applications of the abstract half-period law. *)
Lemma real_sine_period x:S (x+(p+p))=S x.
Proof. by rewrite addrA !(real_sine_half_period ht) opprK. Qed.

(** Source for [real_sine_full_multiplicity]: infinite
    multiplicity of each attained level in the first
    example of Federer 3.2.7, p. 246.
    The principal inverse supplies an actual preimage. *)
Theorem real_sine_full_multiplicity y:
  -1<=y -> y<= 1 ->
  @mapping_multiplicity R [the choiceType of real_line_metric R] R S setT y=(+oo : \bar R)%E.
Proof.
move=>hy1 hy2.
have hPer:=@periodic_mapping_multiplicity_infinite R R S (p+p)
  (addr_gt0 (real_trigonometry_pi_positive ht) (real_trigonometry_pi_positive ht)) real_sine_period (A y).
by rewrite (real_arcsine_sine ht hy1 hy2) in hPer.
Qed.

(** Source for [real_sine_principal_branch_fibre]: the
    single regular branch supporting the nonmeasurability
    argument for the first example in Federer 3.2.7,
    p. 246. Closed endpoints include both extreme levels. *)
Lemma real_sine_principal_branch_fibre y:
  -1<=y -> y<= 1 ->
  mapping_fibre S (`[-(p/2),p/2]:set (real_line_metric R)) y=[set A y].
Proof.
move=>hy1 hy2; have [hAl hAu]:=real_arcsine_range ht hy1 hy2.
apply/seteqP; split=>x.
- move=>[hx hSx]; move:hx; rewrite /= in_itv /= =>/andP[hxl hxu].
  exact (real_sine_branch_injective ht hxl hxu hAl hAu
    (eq_trans hSx (Logic.eq_sym (real_arcsine_sine ht hy1 hy2)))).
- move=>hEq; rewrite hEq; split.
  + by rewrite /= in_itv /= hAl hAu.
  + exact (@real_arcsine_sine R S C A p ht y hy1 hy2).
Qed.
End Basic.
