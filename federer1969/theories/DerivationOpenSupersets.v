(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext BorelRegularMeasureUP
  FiniteOpenMeasureCover ContinuousPartOpenApproximation BorelOpenApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_open_superset]: supporting open
    approximation for the class-M/lattice-regularity observation
    in Federer 2.9.10, p. 157. Apply 2.2.2(2), p. 61,
    to a Borel hull and the countable finite open cover implied
    by M. This returns actual supersets, rather than almost covers. *)
Lemma derivation_measure_open_superset (R : realType) (X : metricType R)
    (phi : set X -> \bar R) S (e : R) :
  is_derivation_measure phi -> (0<e)%R ->
  exists W, open W /\ S `<=` W /\ phi W<=phi S+e%:E.
Proof.
move=> hphi he.
have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have [B [hSB [hB hmass]]] := borel_regular_cover hr S.
have [U hU] := @derivation_measure_finite_open_cover R X phi hphi.
have hUn n : open (U n) /\ phi (U n)< +oo.
  split; [exact: finite_open_cover_open hU n|exact: finite_open_cover_finite hU n].
have hcover : B `<=` \bigcup_n U n by move=> x _; exact: finite_open_cover_covers hU x Logic.I.
have [W [hW [hBW herr]]] := @metric_borel_open_approximation R X phi hm B U e
  (borel_regular_open_measurable hr) hB hUn hcover he.
exists W; split=> //; split; first exact: subset_trans hSB hBW.
have hBm := @borel_regular_borel_measurable R X phi hm hr B hB.
have heq : W `&` B=B.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hBW x hx.
rewrite (hBm W) heq -hmass; exact: leeD (lexx _) (ltW herr).
Qed.
