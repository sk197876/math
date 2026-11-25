(** Open infimum used by Federer (1969), 2.10.18(3), p. 181: a finite Borel
    regular measure equals the infimum of its open covers. This is the cited
    2.2.2–2.2.3, pp. 61–62, applied to the finite restriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP BorelRegularApproximation
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_regular_open_infimum]: supporting
    open-infimum assertion of 2.10.18(3), p. 181.
    The target B is arbitrary; a Borel hull reduces
    it to the measurable open-approximation theorem. *)
Lemma finite_borel_regular_open_infimum (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (B : set X) (x : \bar R) :
  is_measure mu -> is_borel_regular_measure mu -> mu setT < +oo ->
  (forall V, open V -> B `<=` V -> x<=mu V) -> x<=mu B.
Proof.
move=> hm hr hfinite hbound.
have hBfin : mu B < +oo := le_lt_trans (@measure_mono R X mu hm B setT (subsetT B)) hfinite.
have hBnum : mu B \is a fin_num by rewrite (ge0_fin_numE (@measure_nonnegative R X mu hm B)).
pose m := fine (mu B).
have hBm : mu B=m%:E by rewrite /m fineK.
rewrite hBm.
apply: (@extended_upper_bound_from_scaled_errors R x m 1%R (@ler01 R))=> e he.
have [C [hBC [hC hmass]]] := borel_regular_cover hr B.
have hCm := @borel_regular_borel_measurable R X mu hm hr C hC.
have hcover : C `<=` \bigcup_(n in [set: nat]) (@setT X) by move=> y hy; exists 0%N.
have hV (n : nat) : open (@setT X) /\ mu setT < +oo by split=> //; exact: openT.
have [V [ho [hCV herr]]] := @borel_regular_open_approximation R X mu hm hr C
  (fun _ : nat => setT) e hCm hV hcover he.
have hBV : B `<=` V by move=> y hy; exact: hCV (hBC y hy).
have heVC : V `&` C=C by apply/seteqP; split=> [y [_ hy]//|y hy]; split=> //; exact: hCV.
have hh := hbound V ho hBV.
rewrite (hCm V) heVC -hmass in hh.
have hfinal := le_trans hh (leeD2l (mu B) (ltW herr)).
rewrite hBm -EFinD in hfinal.
by rewrite mul1r.
Qed.
