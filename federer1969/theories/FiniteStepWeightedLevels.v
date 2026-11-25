(** Federer (1969), 2.10.24, p. 187: supporting passage from an upper step
    function to a countable finite-mass characteristic expansion. The
    step-function sum is exactly 2.4.1, pp. 80–81; upper functions are
    2.4.2, p. 81. Discard null positive fibres and zero contributions before
    enumeration. All retained coefficients are finite nonnegative reals and
    all retained fibres have finite mass. No measurability of the dominated
    function f is assumed. Source context: WeightedMetricEnvelopeUP.v *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureStepFunctionUP MeasureStepFibres
  MeasureStepNonnegative MeasureIntegralUP NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  NumericalSum CountableCostEnumeration WeightedLevelCoverBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_upper_step_weighted_levels]: supporting
    countable expansion for the upper-integral comparison
    in 2.10.24, p. 187. Null positive
    fibres are removed using almost-everywhere domination;
    the total level cost equals the assigned
    step integral, including a zero assigned value. *)
Theorem finite_upper_step_weighted_levels (R : realType) (X : choiceType)
    (psi : set X -> \bar R) (f : X -> extended_real_line R)
    (u : partial_function X (real_line_metric R)) (a : \bar R) :
  is_measure psi -> (forall x, 0<=f x) ->
  is_measure_upper_function psi (partial_function_total f) u ->
  is_measure_step_integral psi u a -> a< +oo ->
  exists (A : nat -> set X) (w : nat -> R),
    (forall n, (0<=w n)%R) /\ (forall n, psi (A n)< +oo) /\
    nonnegative_sum setT (fun n=>(w n)%:E*psi (A n))=a /\
    measure_almost_everywhere psi [set x | f x<=weighted_level_sum A w x].
Proof.
move=> hm hf hu hi hfinite.
pose F (y : R) := partial_function_preimage u [set y].
pose c (y : R) := y%:E*psi (F y).
have hun : measure_almost_everywhere psi (partial_real_nonnegative_locus u).
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hu.2).
  move=> x [y [z [huy [hfz hzy]]]]; exists y; split=> //.
  have heq : f x=z := hfz.
  have hfy : f x<=y%:E by rewrite heq.
  have hpos : 0<=y%:E := le_trans (hf x) hfy.
  by move: hpos; rewrite lee_fin.
have hc y : 0<=c y := @measure_step_nonnegative_coefficients R X psi hm u hun y.
have hsum : nonnegative_sum setT c=a.
  have hh := hi; rewrite /is_measure_step_integral (numerical_sum_nonnegative (fun y _=>hc y)) in hh.
  by case: hh.
pose D := partial_function_range u `&` [set y | 0<c y].
have hD : countable D := sub_countable (subset_card_le (fun y (hy : D y)=>hy.1))
  (step_function_countable_range hu.1).
have hzero : nonnegative_sum (setT `\` D) c=0.
  apply: nonnegative_sum_zero=> y [_ hyD].
  case: (pselect (partial_function_range u y))=> [hyR|hyR].
  - apply/eqP; rewrite eq_le (hc y) andbT leNgt; apply/negP=> hypos.
    apply: hyD; by split.
  - by rewrite /c /F (partial_fibre_outside_range hyR) (measure_empty hm) mule0.
have hsumD : nonnegative_sum D c=a.
  have hh := hsum; rewrite (@nonnegative_sum_split R [the choiceType of real_line_metric R] setT D c (fun y _=>hc y)) setTI hzero adde0 in hh.
  exact hh.
have hc0 : c 0%R=0 by rewrite /c mul0e.
have [v [hv [hcover hcost]]] := @countable_zero_cost_enumeration R [the choiceType of real_line_metric R] D c 0%R hD hc0 (fun y _=>hc y).
have hpositive y (hy : D y) : (0<y)%R.
  case: (ltP 0%R y)=> // hyn.
  have hyE : y%:E<=0 by rewrite lee_fin.
  have hh : c y<=0 := mule_le0_ge0 hyE (@measure_nonnegative R X psi hm (F y)).
  by have hbad := lt_le_trans hy.2 hh; rewrite ltxx in hbad.
have hfibre y (hy : D y) : psi (F y)< +oo.
  have hpos : 0<y%:E by rewrite lte_fin; exact: hpositive y hy.
  have hterm : c y<=a.
    rewrite -hsum; exact: (@nonnegative_sum_term R [the choiceType of real_line_metric R] setT c y Logic.I).
  case heq: (psi (F y)); first exact: ltry; last by [].
  have hh := le_lt_trans hterm hfinite.
  by rewrite /c heq (gt0_muley hpos) ltxx in hh.
pose A n := if v n==0%R then set0 else F (v n).
pose w n := v n.
have hw n : (0<=w n)%R.
  have [hn|hn] := hv n; [exact: ltW (hpositive _ hn)|by rewrite /w hn].
have hA n : psi (A n)< +oo.
  rewrite /A; case hn: (v n==0%R); first by rewrite (measure_empty hm) ltry.
  have [hDvn|heq] := hv n; first exact: hfibre _ hDvn.
  by rewrite heq eqxx in hn.
have hcostn n : (w n)%:E*psi (A n)=c (v n).
  rewrite /w /A; case hn: (v n==0%R); last by [].
  have heq : v n=0%R := eqP hn; by rewrite heq /c !mul0e.
have htotal : nonnegative_sum setT (fun n=>(w n)%:E*psi (A n))=a.
  have heq : (fun n=>(w n)%:E*psi (A n))=(fun n=>c (v n)) by apply: funext=> n; exact: hcostn.
  by rewrite heq hcost hsumD.
pose B := partial_function_range u `&` [set y | (0<y)%R /\ psi (F y)=0].
pose Z := \bigcup_(y in B) F y.
have hB : countable B := sub_countable (subset_card_le (fun y (hy : B y)=>hy.1))
  (step_function_countable_range hu.1).
have hZ : psi Z=0.
  apply: (@measure_null_countable_union R X [the choiceType of real_line_metric R] psi hm B F hB)=> y hy; exact hy.2.2.
have hoff : measure_almost_everywhere psi (~` Z) by rewrite /measure_almost_everywhere setCK.
have hdom : measure_almost_everywhere psi [set x | f x<=weighted_level_sum A w x].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ (measure_almost_everywhere_and hm hu.2 hoff)).
  move=> x [[y [z [huy [hfz hzy]]]] hxZ].
  have heq : f x=z := hfz.
  have hfy : f x<=y%:E by rewrite heq.
  have hy0 : (0<=y)%R by have hh := le_trans (hf x) hfy; rewrite lee_fin in hh.
  case: (eqVneq y 0%R)=> [hyzero|hyneq].
  - apply: le_trans hfy _; rewrite hyzero; exact: nonnegative_sum_nonnegative.
  - have hypos : (0<y)%R by rewrite lt_neqAle eq_sym hyneq hy0.
    have hF : F y x by exists y; split.
    have hyR : partial_function_range u y by exists x.
    have hmpos : 0<psi (F y).
      case: (ltP 0 (psi (F y)))=> // hle.
      have hnull : psi (F y)=0 by apply/eqP; rewrite eq_le hle (measure_nonnegative hm (F y)).
      exfalso; apply: hxZ; exists y=> //; split=> //; by split.
    have hyE : 0<y%:E by rewrite lte_fin.
    have hyD : D y by split=> //; exact: mule_gt0 hyE hmpos.
    have [n hn] := hcover y hyD.
    have hxA : x \in A n.
      apply: mem_set; rewrite /A hn (negbTE hyneq); exact hF.
    have hh := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
      (fun k=>if x \in A k then (w k)%:E else 0) n Logic.I.
    rewrite hxA /w hn in hh; exact: le_trans hfy hh.
exists A,w; by split=> //; split=> //; split.
Qed.
