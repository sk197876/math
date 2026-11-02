(** Federer (1969), 2.9.20, p. 166: cover a null set by open sets of
    arbitrarily small measure, using 2.2.2–2.2.3, pp. 61–62. This supporting
    cover law retains the original class M. Source context:
    RealAbsoluteContinuityUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic MeasureFiniteClosure
  MeasureDerivationContext BorelRegularMeasureUP BorelRegularApproximation
  ContinuousPartOpenApproximation FiniteOpenMeasureCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_null_open_cover]: supporting open null-set
    approximation for the implication (3)=>(4) in Federer 2.9.20, p. 166 A
    null set, without a Borel-set hypothesis, has an actual open superset of
    measure below each positive number. Apply the already proved open
    approximation theorem to the measurable null set. *)
Lemma derivation_null_open_cover (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (N : set X) (d : R) :
  is_derivation_measure phi -> phi N=0 -> (0<d)%R ->
  exists W, open W /\ N `<=` W /\ phi W<d%:E.
Proof.
move=> hphi hN hd.
have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have hNm := @measure_null_measurable R X phi hm N hN.
have [U hU] := @derivation_measure_finite_open_cover R X phi hphi.
have hUn n : open (U n) /\ phi (U n)< +oo.
  split; [exact: finite_open_cover_open hU n|exact: finite_open_cover_finite hU n].
have hcover : N `<=` \bigcup_n U n.
  by move=> x _; exact: finite_open_cover_covers hU x Logic.I.
have [W [hW [hNW hSmall]]] := @borel_regular_open_approximation R X phi hm hr N U d
  hNm hUn hcover hd.
have hWN : phi (W `&` N)=0.
  apply: (@measure_null_subset R X phi hm _ N) hN; by move=> x [].
exists W; split=> //; split=> //.
by rewrite (hNm W) hWN add0e.
Qed.
