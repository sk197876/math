(** The nonnegative quotient and its locally nonempty domain, supporting
    Federer (1969), 2.9.5, pp. 154–155. Outside the fine-null-cell
    exceptional set P, small bounded Vitali cells have nonzero finite
    denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext
  MeasureDerivates ExtendedRealConventions PartialFunctionUP CoveringRelationUP
  CoveringRelationFineness CoveringRelationLimits CoveringFamilyUP MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_ratio_nonnegative]: supporting sign
    assertion for the conclusion 0<=D in Federer 2.9.5,
    p. 154. Only defined ordinary quotients of
    nonnegative measure values are considered. *)
Lemma measure_ratio_nonnegative (R : realType) (X : choiceType)
    (psi phi : set X -> \bar R) S y :
  is_measure psi -> is_measure phi ->
  partial_function_graph (measure_ratio_function psi phi) S y -> 0<=y.
Proof.
move=> hp hf; rewrite /measure_ratio_function /= /extended_divide.
case: ifP=> // _ [<-]; apply: mule_ge0; first exact (@measure_nonnegative R X psi hp S).
by rewrite inve_ge0; exact (@measure_nonnegative R X phi hf S).
Qed.

(** Source for [measure_ratio_lower_limit_nonnegative]: sign
    of the lower covering limit used in Federer 2.9.5,
    pp. 154–155. Empty quotient ranges have infimum
    positive infinity, so the assertion does not require
    domain fineness and does not imply existence of a derivate. *)
Lemma measure_ratio_lower_limit_nonnegative (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_measure psi -> is_measure phi ->
  0<=covering_lower_limit V (measure_ratio_function psi phi) x.
Proof.
move=> hp hf.
apply: le_trans _ (@covering_lower_limit_ge_level R X V (measure_ratio_function psi phi) x 1%R (@ltr01 R)).
apply: extended_real_inf_greatest=> y [S [_ [_ hy]]].
exact: measure_ratio_nonnegative hp hf hy.
Qed.

(** Source for [nonfine_null_fiber_positive_scale]: supporting domain
    reduction for P in Federer 2.9.5, p. 154 Failure of null-cell fineness
    gives one positive scale at which every related cell has nonzero
    measure. *)
Lemma nonfine_null_fiber_positive_scale (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  ~ covering_relation_fine_at (fun x S => V x S /\ phi S=0) x ->
  exists e : R, (0<e)%R /\ forall S, V x S ->
    extended_metric_diameter S<e%:E -> phi S!=0.
Proof.
move=> hn; apply: contrapT=> hnone; apply: hn.
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
apply: contrapT=> hno.
apply: hnone; exists e; split=> // S hS hd; apply/eqP=> hz.
apply: hno; exists S; by split=> //; split.
Qed.

(** Source for [derivation_ratio_domain_fine]: the domain qualification
    behind the exceptional-set argument of Federer 2.9.5, p. 154 Outside P,
    arbitrarily small Vitali cells lie in the partial quotient's domain.
    Boundedness provides finite denominator values under the original M. *)
Lemma derivation_ratio_domain_fine (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (V : X -> set X -> Prop) x :
  is_derivation_measure phi -> covering_relation_fine_at V x ->
  ~ covering_relation_fine_at (fun x S => V x S /\ phi S=0) x ->
  covering_relation_fine_at (fun x S => V x S /\
    partial_function_domain (measure_ratio_function psi phi) S) x.
Proof.
move=> hphi hf hn.
have [d [hd hnz]] := @nonfine_null_fiber_positive_scale R X phi V x hn.
apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
pose t := (Num.min e (Num.min d 1))%R.
have ht : (0<t)%R by rewrite /t !lt_min he hd ltr01.
have hte : (t<=e)%R by rewrite /t ge_min lexx.
have hti : (t<=Num.min d 1)%R by rewrite /t ge_min lexx orbT.
have htd : (t<=d)%R by apply: le_trans hti _; rewrite ge_min lexx.
have ht1 : (t<=1)%R by apply: le_trans hti _; rewrite ge_min lexx orbT.
have [S [hS hdiam]] := (covering_relation_fine_iff_small_diameter V x).1 hf t ht.
have hSd : extended_metric_diameter S<d%:E.
  apply: lt_le_trans hdiam _; by rewrite lee_fin.
have hS1 : extended_metric_diameter S<1.
  apply: lt_le_trans hdiam _; by rewrite lee_fin.
have hbounded : metric_set_bounded S := lt_trans hS1 (@ltry R 1%R).
have hfinite : phi S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law hphi) S)).
  exact: derivation_measure_bounded_finite hphi S hbounded.
have hpos : 0<phi S by rewrite lt_def (hnz S hS hSd) (measure_nonnegative (derivation_measure_law hphi)).
exists S; split.
- split=> //; exists (psi S/phi S); exact: measure_ratio_positive_finite_denominator hpos hfinite.
- apply: lt_le_trans hdiam _; by rewrite lee_fin.
Qed.
