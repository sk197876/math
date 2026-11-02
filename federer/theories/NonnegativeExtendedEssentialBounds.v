(** Supporting essential bounds for Federer (1969), 2.10.5(2), p. 173: on
    the projection probability space, lower-continuous nonnegative volume
    functions have essential supremum equal to their supremum. Prove the
    needed order facts from the infinity formula of 2.4.12, p. 86, including
    extended-valued inputs. The full-support and open-superlevel hypotheses
    below are proved separately for the actual projection measure and open
    source sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP
  NonnegativeExtendedExponentNormUP MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_threshold_upward]:
    supporting monotonicity of the null-superlevel
    bounds used for the infinity formula in
    Federer 2.10.5(2), p. 173. *)
Lemma nonnegative_extended_threshold_upward (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> \bar R) (r s : \bar R) :
  nonnegative_extended_essential_thresholds mu f r -> r<=s ->
  nonnegative_extended_essential_thresholds mu f s.
Proof.
move=> [hr hz] hrs; split; first exact: le_trans hr hrs.
apply: (@measure_null_subset R X mu hm _ _ _ hz)=> x hx.
exact: le_lt_trans hrs hx.
Qed.

(** Source for [nonnegative_extended_essential_strict_upper]:
    supporting feasibility of every bound strictly
    above the essential supremum in Federer
    2.10.5(2), p. 173, from the infimum
    formula of 2.4.12, p. 86. No
    measurability of the function is needed here. *)
Lemma nonnegative_extended_essential_strict_upper (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : X -> extended_real_line R) (a r : \bar R) :
  is_nonnegative_extended_exponent_norm mu f +oo a -> a<r ->
  nonnegative_extended_essential_thresholds mu f r.
Proof.
move=> hn har.
case: (pselect (exists s, nonnegative_extended_essential_thresholds mu f s /\ s<r))=> [h|hno].
- have [s [hs hsr]] := h.
  exact: (@nonnegative_extended_threshold_upward R X mu hm f s r hs (ltW hsr)).
- exfalso; have hra : r<=a.
    apply: hn.2=> s hs.
    rewrite leNgt; apply/negP=> hsr; apply: hno; by exists s.
  by move: har; rewrite ltNge hra.
Qed.

(** Source for [nonnegative_extended_essential_supremum]:
    supporting essential-supremum identification
    for the infinity comparison in Federer
    2.10.5(2), p. 173. On a nonempty
    parameter space with positive mass on every
    nonempty open set, open strict superlevels
    suffice; boundedness and full continuity are
    unnecessary for this supporting generalization. *)
Theorem nonnegative_extended_essential_supremum (R : realType) (P : topologicalType)
    (mu : set P -> \bar R) (hm : is_measure mu)
    (f : P -> extended_real_line R) (a : \bar R) :
  (exists p : P, True) -> (forall p, 0<=f p) ->
  (forall r : R, open [set p | r%:E<f p]) ->
  (forall U : set P, open U -> (exists p, U p) -> 0<mu U) ->
  is_nonnegative_extended_exponent_norm mu f +oo a ->
  is_extended_real_supremum (f @` setT) a.
Proof.
move=> [p0 _] hf0 hopen hpos hn; constructor.
- move=> b [p _ <-]; rewrite leNgt; apply/negP=> hbad.
  have [q [haq hqf]] := @extended_rationals_order_dense R a (f p) hbad.
  have [_ hz] := @nonnegative_extended_essential_strict_upper R _ mu hm f a (ratr q : R)%:E hn haq.
  have hpositive := hpos [set p | (ratr q : R)%:E<f p] (hopen (ratr q)) (ex_intro _ p hqf).
  by rewrite hz ltxx in hpositive.
- move=> c hc.
  have hfc p : f p<=c by apply: hc; by exists p.
  apply: hn.1; split; first exact: le_trans (hf0 p0) (hfc p0).
  have he : [set p | c<f p]=set0.
    apply/seteqP; split=> p; last by [].
    by rewrite /= ltNge hfc.
  rewrite he; exact: measure_empty hm.
Qed.
