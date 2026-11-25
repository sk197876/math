(** Federer (1969), 2.10.28, p. 193: f is locally constant off the closed
    limit set, and its actual two-sided derivative is zero there. Derive the
    assertion from the abstract cumulative equation for a restricted
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureRestriction
  FiniteCumulativeFunctionUP FiniteCumulativeFunctionLaws RealCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [restricted_cumulative_vanishing_increment]: supporting
    equal cumulative values across a gap of A
    in 2.10.28, p. 193. The half-open
    gap convention follows from the closed
    lower rays in the defining equation. *)
Lemma restricted_cumulative_vanishing_increment (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (A : set R) (f : R -> R)
    (hf : is_finite_cumulative_function (measure_restrict mu A) f)
    (hray : forall x : R, measure_measurable mu [set z | z<=x]) a b :
  a<=b -> (A `&` ([set z | z<=b] `\` [set z | z<=a]))=set0 -> f a=f b.
Proof.
move=> hab hgap.
have hn := measure_restrict_is_measure hm A.
have hmeas := @measure_restrict_measurable R R mu A [set z | z<=a] (hray a).
have hh := @finite_cumulative_function_increment R (measure_restrict mu A) hn f hf a b hab hmeas.
rewrite /measure_restrict hgap (measure_empty hm) in hh.
have hz : f b-f a=0 := EFin_inj (esym hh).
lra.
Qed.

(** Source for [restricted_cumulative_gap_neighbourhood]: supporting
    local constancy used for f'(x)=0 off A
    in 2.10.28, p. 193. Any ball
    disjoint from A contains no mass between
    its centre and another point of the ball. *)
Lemma restricted_cumulative_gap_neighbourhood (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (A : set R) (f : R -> R)
    (hf : is_finite_cumulative_function (measure_restrict mu A) f)
    (hray : forall x : R, measure_measurable mu [set z | z<=x]) (x d : R) :
  0<d -> (forall z, `|z-x|<d -> ~A z) ->
  forall y, `|y-x|<d -> f y=f x.
Proof.
move=> hd hgap y; rewrite ltr_norml=> /andP[hyl hyr].
case: (leP x y)=> hxy.
- symmetry; apply: (@restricted_cumulative_vanishing_increment R mu hm A f hf hray x y hxy).
  apply/seteqP; split=> [z [hzA [hzy /negP hzx]]|z []].
  change (is_true (z<=y)) in hzy.
  have hxz : x<z by rewrite ltNge.
  have hsmall : `|z-x|<d by rewrite ltr_norml; apply/andP; split; lra.
  exact (hgap z hsmall hzA).
- apply: (@restricted_cumulative_vanishing_increment R mu hm A f hf hray y x (ltW hxy)).
  apply/seteqP; split=> [z [hzA [hzx /negP hzy]]|z []].
  change (is_true (z<=x)) in hzx.
  have hyz : y<z by rewrite ltNge.
  have hsmall : `|z-x|<d by rewrite ltr_norml; apply/andP; split; lra.
  exact (hgap z hsmall hzA).
Qed.

(** Source for [restricted_cumulative_derivative_off_closed_set]: direct
    f'(x)=0 for x outside A in 2.10.28,
    p. 193, where A is closed. This
    is the actual punctured difference-quotient
    limit of 2.9.19, not a selected derivative
    value or an almost-everywhere definition. *)
Theorem restricted_cumulative_derivative_off_closed_set (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (A : set (real_line_metric R)) (f : R -> R)
    (hf : is_finite_cumulative_function (measure_restrict mu A) f)
    (hray : forall x : R, measure_measurable mu [set z | z<=x]) :
  closed A -> forall x, ~A x -> has_real_curve_derivative f x 0.
Proof.
move=> hA x hx.
have hn : nbhs (x : real_line_metric R) (~` A).
  apply: open_nbhs_nbhs; split=> //; exact: closed_openC hA.
have [d hd hsub] := (nbhs_ballP (x : real_line_metric R) _).1 hn.
have hgap z : `|z-x|<d -> ~A z.
  move=> hz; apply: hsub; by rewrite /= real_line_ball_distance /= distrC.
have hconstant := @restricted_cumulative_gap_neighbourhood R mu hm A f hf hray x d hd hgap.
move=> e he; exists d; split=> // t /andP[ht0 htd].
have hxt : `|x+t-x|<d by rewrite addrAC subrr add0r.
by rewrite (hconstant (x+t) hxt) subrr mul0r subr0 normr0.
Qed.
