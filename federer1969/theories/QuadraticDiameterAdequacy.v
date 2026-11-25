(** A quantitative consequence of Federer (1969), 2.8.7, p. 144, used to
    assemble the finite fans for 2.8.20, p. 152. Families whose area
    controls squared diameter have bounded enlargement ratios when ball
    areas have a quadratic upper bound. Applying the already proved covering
    theorem to fan unions replaces the repeated finite packing of Saks1934
    Lemma B, pp. 258–259, and Cesari1939 Lemma III, pp. 306–307. This
    proof-route departure is local, not a correction to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring lra.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls MetricDiameter MetricDiameterUP
  CoveringFamilyUP DiametricRegularityUP DiameterWeightLaws WeightedEnlargements EnlargementAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [diameter_enlargement_at_member]: supporting
    triangle-inequality estimate for the application of Federer
    2.8.7 to the fan unions in 2.8.20, p. 152.
    It generalises the ball estimate of 2.8.8, p. 145,
    to any member with a real diameter weight. *)
Lemma diameter_enlargement_at_member (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) (tau : R) (S : set X) (a : X) :
  is_real_diameter_weight F d -> F S -> S a ->
  weighted_enlargement F d tau S `<=` metric_closed_ball a ((1+tau)*d S)%R.
Proof.
move=> hd hS ha x [T [hT [hmeet hweight]] hx].
have hn : T `&` S != set0 by apply/eqP.
have [y [hyT hyS]] := (set0P _).1 hn.
have hay : (mdist a y <= d S)%R.
  have hb := metric_diameter_upper (hd S hS) ha hyS; by rewrite lee_fin in hb.
have hyx : (mdist y x <= d T)%R.
  have hb := metric_diameter_upper (hd T hT) hyT hx; by rewrite lee_fin in hb.
have hb := le_trans (metric_triangle a y x) (lerD hay (le_trans hyx hweight)).
by rewrite /metric_closed_ball /= mulrDl mul1r.
Qed.

(** Source for [quadratic_diameter_family_adequate]: supporting
    consequence of Federer 2.8.7, p. 144, for the
    fan-union selection used in 2.8.20, p. 152.
    The strict enlargement constant is obtained by adding one;
    positive member measure, bounded weights and the original
    standing metric-measure hypotheses are explicit. *)
Theorem quadratic_diameter_family_adequate (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) (d : set X -> R)
    (A : set X) (M c : R) :
  is_covering_theory_context F mu -> is_real_diameter_weight F d ->
  (exists B, forall S, F S -> (d S<=B)%R) -> family_covers_finely F A ->
  (0<=M)%R -> (0<c)%R ->
  (forall a r, (0<=r)%R -> mu (metric_closed_ball a r) <= (M*r*r)%:E) ->
  (forall S, F S -> 0<mu S /\ (c*d S*d S)%:E <= mu S) ->
  family_is_measure_adequate mu F A.
Proof.
move=> hc hd hb hf hM hcp hball hmass.
pose L := (M*9/c)%R.
have h9 : (0<=9 :> R)%R by rewrite ler0n.
have hL : (0<=L)%R := divr_ge0 (mulr_ge0 hM h9) (ltW hcp).
have hLc : (L*c=9*M)%R by rewrite /L divfK ?gt_eqF // mulrC.
have hlambda : (1<L+2)%R by lra.
have hbound S (hS : F S) :
    mu (weighted_enlargement F d 2 S) < (L+2)%:E * mu S.
  have [hpos hlow] := hmass S hS.
  have hne : S != set0.
    apply/eqP=> he; move: hpos; by rewrite he (measure_empty (covering_context_measure hc)) ltxx.
  have [a ha] := (set0P _).1 hne.
  have hd0 := @diameter_weight_nonnegative R X F d hd S hS.
  have hsub := @diameter_enlargement_at_member R X F d 2 S a hd hS ha.
  have h3 : (0<=1+2 :> R)%R by rewrite addr_ge0 ?ler0n.
  have hr : (0<=(1+2)*d S)%R := mulr_ge0 h3 hd0.
  have hup := le_trans (@measure_mono R X mu (covering_context_measure hc) _ _ hsub)
    (hball a ((1+2)*d S)%R hr).
  have hLE : (0<=L%:E)%E by rewrite lee_fin.
  have hscaled := lee_wpmul2l hLE hlow.
  have he1 : (M*((1+2)*d S)*((1+2)*d S)=(9*M)*(d S*d S))%R by ring.
  have he2 : (L*(c*d S*d S)=(L*c)*(d S*d S))%R by ring.
  have he : (M*((1+2)*d S)*((1+2)*d S)=L*(c*d S*d S))%R.
    by rewrite he1 he2 hLc.
  have hbnd : mu (weighted_enlargement F d 2 S) <= L%:E * mu S.
    apply: le_trans hup _; by rewrite he EFinM.
  have hSbounded : metric_set_bounded S.
    rewrite /metric_set_bounded
      (@metric_diameter_unique R X S (extended_metric_diameter S) (d S)%:E
        (extended_metric_diameter_specification S) (hd S hS)); exact: ltry.
  have hSfin : mu S \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative (covering_context_measure hc) S)).
    exact (@covering_context_bounded_finite R X F mu hc S hSbounded).
  pose q := fine (mu S).
  have hq : mu S=q%:E by rewrite /q fineK.
  have hqp : (0<q)%R by move: hpos; rewrite hq lte_fin.
  apply: le_lt_trans hbnd _; rewrite hq -!EFinM lte_fin mulrDl.
  have hp2 : (0<2*q)%R by rewrite mulr_gt0 ?ltr0n.
  lra.
have ht : (1<2 :> R)%R by rewrite ltr1n.
exact (@enlargement_control_adequacy R X F mu d 2 (L+2)%R A hc
  (diameter_weight_nonnegative hd) hb ht hlambda hbound hf).
Qed.
