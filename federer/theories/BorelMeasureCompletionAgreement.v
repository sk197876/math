(** Federer (1969), 2.10.45, p. 203, conclusion: the equality obtained on
    Borel sets holds for every Lebesgue-measurable U, as stated on p. 202.
    The supporting completion argument uses the Borel sandwich of 2.2.3, p.
    61, and countable exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  MeasureCountableClosure MeasureContinuityBelow ExtendedIncreasingLimitSupremum
  BorelRegularMeasureUP BorelRegularSandwich BorelNullTransfer TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_agreement_finite_completion]: supporting
    finite-measure completion step in 2.10.45, p. 203.
    Agreement on Borel sets with a Borel regular measure
    determines both values and measurability on its finite
    measurable sets. The second measure need not be regular. *)
Theorem borel_agreement_finite_completion (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure nu) :
  (forall B, borel_set B -> measure_measurable mu B) ->
  (forall B, borel_set B -> mu B=nu B) -> forall A,
  measure_measurable nu A -> nu A< +oo ->
    measure_measurable mu A /\ mu A=nu A.
Proof.
move=> hb he A hA hfin.
have hnull B (hB : nu B=0) : mu B=0.
  have [D [hBD [hD hv]]] := borel_regular_cover hr B.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have hh := measure_mono hm hBD; by rewrite (he D hD) -hv hB in hh.
have hAm := @borel_null_transfer_finite_measurable R X nu mu hn hm hr hb hnull A hA hfin.
split=> //.
have [D [B [hD [hB [hDA [hAB hz]]]]]] := borel_regular_finite_sandwich hn hr hA hfin.
have hDB : D `<=` B := subset_trans hDA hAB.
have hi : B `&` D=D.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hDB.
have hval := borel_regular_borel_measurable hn hr hD B.
rewrite hi hz adde0 in hval.
have hnuD := measure_mono hn hDA.
have hnuB := measure_mono hn hAB.
have hmuD := measure_mono hm hDA.
have hmuB := measure_mono hm hAB.
rewrite (he D hD) in hmuD; rewrite (he B hB) hval in hmuB hnuB.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: le_trans hmuB hnuD.
- exact: le_trans hnuB hmuD.
Qed.

(** Source for [borel_agreement_sigma_finite_completion]: supporting
    extension to possibly infinite measurable U in 2.10.45,
    pp. 202–203. An increasing Borel exhaustion of finite
    reference measure suffices. Continuity from below is
    applied after measurability has been proved on each piece. *)
Theorem borel_agreement_sigma_finite_completion (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure nu) (E : nat -> set X) :
  (forall B, borel_set B -> measure_measurable mu B) ->
  (forall B, borel_set B -> mu B=nu B) ->
  (forall n, borel_set (E n)) -> (forall n, nu (E n)< +oo) ->
  (forall n m, (n<=m)%N -> E n `<=` E m) ->
  (forall x, exists n, E n x) -> forall A,
  measure_measurable nu A -> measure_measurable mu A /\ mu A=nu A.
Proof.
move=> hb he hE hEf hEm hcov A hA.
pose F n := A `&` E n.
have hFn n : measure_measurable nu (F n).
  exact (@measure_measurable_intersection R X nu hn A (E n) hA
    (@borel_regular_borel_measurable R X nu hn hr (E n) (hE n))).
have hFf n : nu (F n)< +oo.
  apply: le_lt_trans (measure_mono hn _) (hEf n); by move=> x [_ hx].
have hFm n := @borel_agreement_finite_completion R X mu nu hm hn hr hb he (F n) (hFn n) (hFf n).
have hmono n m (hnm : (n<=m)%N) : F n `<=` F m.
  move=> x [hx hn']; split=> //; exact: hEm n m hnm x hn'.
have hwhole : (\bigcup_n F n)=A.
  apply/seteqP; split=> x; first by move=> [n _ [hx _]].
  move=> hx; have [n hn'] := hcov x; exists n=> //; by split.
have hAm : measure_measurable mu A.
  rewrite -hwhole; exact (@measure_measurable_sequence_union R X mu hm F (fun n=>(hFm n).1)).
split=> //.
have hlimm := @measure_continuity_below R X mu hm F (fun n=>(hFm n).1) hmono.
have hlimn := @measure_continuity_below R X nu hn F hFn hmono.
rewrite hwhole in hlimm hlimn.
have heq : (fun n=>mu (F n))=(fun n=>nu (F n)).
  apply: funext=> n; exact: (hFm n).2.
rewrite heq in hlimm.
exact: extended_order_limit_unique hlimm.2 hlimn.2.
Qed.
