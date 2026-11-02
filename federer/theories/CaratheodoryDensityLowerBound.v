(** Corrected Federer (1969), 2.10.17(3), p. 179: the subcritical density
    locus has final measure zero. Retain the printed intersection and
    finite-approximation hypotheses. The B-set exhaustion here uses positive
    rational thresholds below one and reciprocal natural cutoffs, a
    countable two-index expansion of the printed diagonal exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover NonnegativeSum
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleLocalAgreement
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryBorelRegular
  CaratheodoryDensityFunction CaratheodoryDensityUpperBound CaratheodoryDensityGoodSets CaratheodoryDensityGoodNull
  ExtendedRealOrderTopology CoveringRelationUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_density_subcritical_null]: supporting
    subcritical-locus assertion for corrected 2.10.17(3), p. 179 The proof
    covers the locus by countably many null B-sets. It also covers a
    negative upper limit without requiring fineness as a separate premise in
    this supporting form. *)
Theorem caratheodory_density_subcritical_null (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (omega psi : set X -> \bar R) (A : set X) :
  (forall S, F S -> 0<=c S) ->
  (forall S T, F S -> F T -> F (S `&` T) /\ c (S `&` T)<=c T) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) +oo omega ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall delta : \bar R, 0<delta ->
    metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta A < +oo) ->
  psi [set x | A x /\ covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function omega c A) x<1]=0.
Proof.
move=> hc hclosed ho hpsi hfinite.
pose J := [the choiceType of set_type F].
pose S (j : J) := (val j : set X).
pose z (j : J) := c (val j).
have hz j : 0<=z j by apply: hc; exact: set_valP.
have hInt : is_intersection_cost_family S z.
  move=> j k; have [hF hcost] := hclosed (S j) (S k) (set_valP j) (set_valP k).
  pose l : set_type F := @exist (set X) (fun B => B \in F) (S j `&` S k) (mem_set hF).
  exists l; split=> //.
have hm := @caratheodory_limit_is_measure R X J S z psi hpsi hz.
have homega := @metric_scale_envelope_is_measure R X J S z +oo omega ho hz.
pose K := [the choiceType of ((rat*nat)%type : Type)].
pose D : set K := [set p | (0<(ratr p.1 : R)<1)%R].
pose d k := (((k.+1)%:R : R)^-1)%:E.
pose B (p : K) := caratheodory_density_good_set S z omega A (ratr p.1) (d p.2).
have hD : countable D := countableP D.
have hnull p : D p -> psi (B p)=0.
  move=> hp.
  exact (@caratheodory_density_good_set_null R X J S z omega psi A (ratr p.1) (d p.2)
    hz hInt ho hpsi hfinite hp (reciprocal_metric_cutoff_positive R p.2)).
pose E := [set x | A x /\ covering_upper_limit (caratheodory_family_relation F)
  (caratheodory_density_function omega c A) x<1].
have hcover : E `<=` \bigcup_(p in D) B p.
  move=> x [hx hu].
  pose u := covering_upper_limit (caratheodory_family_relation F) (caratheodory_density_function omega c A) x.
  have hmax : Order.max u 0<1 by rewrite gt_max hu lte_fin ltr01.
  have [q [hl hq]] := @extended_rationals_order_dense R (Order.max u 0) 1 hmax.
  have h0max : 0<=Order.max u 0 by rewrite le_max lexx orbT.
  have humax : u<=Order.max u 0 by rewrite le_max lexx.
  have hq0E : 0<(ratr q : R)%:E := le_lt_trans h0max hl.
  have hq0 : (0<(ratr q : R))%R by move: hq0E; rewrite lte_fin.
  have hq1 : ((ratr q : R)<1)%R by move: hq; rewrite lte_fin.
  have huq : u<(ratr q : R)%:E := le_lt_trans humax hl.
  have hcost T : caratheodory_family_relation F x T -> 0<=c T by move=> [hF _]; exact: hc.
  have [eta [heta hgen]] := @caratheodory_density_upper_local_estimate R X omega homega c
    (caratheodory_family_relation F) A x (ratr q) hq0 hcost huq.
  have [k hk] := reciprocal_metric_cutoffs_cofinal heta.
  exists (q,k); first by apply/andP; split.
  split=> // j hj hdiam.
  apply: hgen _ _ (le_trans hdiam hk); split=> //; exact: set_valP.
apply/eqP; rewrite eq_le (@measure_nonnegative R X psi hm E) andbT.
have hb := @measure_indexed_cover R X K psi hm E D B hD hcover.
by rewrite (nonnegative_sum_zero hnull) in hb.
Qed.

(** Source for [federer_2_10_17_3]: corrected direct null-locus statement of
    2.10.17(3), p. 179. Retain fineness, the printed intersection hypothesis
    and finite positive-cutoff approximations. The printed partial-quotient
    version is not asserted or refuted. *)
Theorem federer_2_10_17_3 (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (omega psi : set X -> \bar R) (A : set X) :
  (forall S, F S -> 0<=c S) ->
  (forall S T, F S -> F T -> F (S `&` T) /\ c (S `&` T)<=c T) ->
  (forall x, covering_relation_fine_at (caratheodory_family_relation F) x) ->
  is_metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) +oo omega ->
  is_caratheodory_limit (fun j : set_type F => val j) (fun j => c (val j)) psi ->
  (forall delta : \bar R, 0<delta ->
    metric_scale_envelope (fun j : set_type F => val j) (fun j => c (val j)) delta A < +oo) ->
  psi [set x | A x /\ 0<=covering_upper_limit (caratheodory_family_relation F)
    (caratheodory_density_function omega c A) x /\
    covering_upper_limit (caratheodory_family_relation F) (caratheodory_density_function omega c A) x<1]=0.
Proof.
move=> hc hclosed hf ho hpsi hfinite.
have he := @caratheodory_density_subcritical_null R X F c omega psi A hc hclosed ho hpsi hfinite.
have hm := @caratheodory_limit_is_measure R X [the choiceType of set_type F]
  (fun j => val j) (fun j => c (val j)) psi hpsi (fun j => hc _ (set_valP j)).
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
rewrite -he; apply: (@measure_mono R X psi hm)=> x [hx [_ hu]]; by split.
Qed.
