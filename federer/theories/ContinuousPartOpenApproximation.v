(** The open almost cover at the start of Federer (1969), 2.9.3, p. 154:
    phi(A minus W)=0 and beta(W)<=beta_phi(A)+epsilon. Attain the
    continuous-part infimum, then apply the established open approximation
    theorem 2.2.2(2), p. 61. The original bounded-set finiteness gives the
    countable finite-measure open cover needed by 2.2.2. Source context:
    CoveringLowerSublevel.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext AbsoluteContinuousPart AbsoluteContinuousPartAttainment
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit BorelRegularMeasureUP
  CoveringFamilyUP FiniteOpenMeasureCover BorelOpenApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_finite_open_cover]: supporting countable
    open cover for the application of 2.2.2 in Federer 2.9.3, p. 154. This
    follows from the original class M and is not a replacement of that
    class. *)
Lemma derivation_measure_finite_open_cover (R : realType) (X : metricType R)
    (psi : set X -> \bar R) :
  is_derivation_measure psi -> exists U, is_finite_open_measure_cover psi U.
Proof.
move=> hpsi.
have hc : is_covering_theory_context set0 psi.
  constructor.
  - exact: derivation_measure_law hpsi.
  - by move=> S [].
  - exact: borel_regular_open_measurable (derivation_measure_borel_regular hpsi).
  - exact: derivation_measure_bounded_finite hpsi.
exact (@covering_context_finite_open_cover R X set0 psi hc).
Qed.

(** Source for [continuous_part_open_almost_cover]: direct supporting choice
    of W in the first display of the proof of Federer 2.9.3, p. 154 The
    target A need not be measurable and the continuous-part value may be
    infinite. *)
Theorem continuous_part_open_almost_cover (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (A : set X) (e : R) :
  is_measure phi -> is_derivation_measure psi -> (0<e)%R ->
  exists W, open W /\ phi (A `\` W)=0 /\
    psi W<=measure_continuous_part psi phi A+e%:E.
Proof.
move=> hphi hpsi he.
have hm := derivation_measure_law hpsi.
have hr := derivation_measure_borel_regular hpsi.
have [B [hB [hz hval]]] := @continuous_part_attained R X phi psi
  (measure_continuous_part psi phi) hphi hm (measure_continuous_part_specification psi phi) A.
have [U hU] := @derivation_measure_finite_open_cover R X psi hpsi.
have hBc : B `<=` \bigcup_n U n.
  move=> x _; exact: finite_open_cover_covers hU x Logic.I.
have hUn n : open (U n) /\ psi (U n)< +oo.
  split; [exact: finite_open_cover_open hU n|exact: finite_open_cover_finite hU n].
have [W [hW [hBW herr]]] := @metric_borel_open_approximation R X psi hm B U e
  (borel_regular_open_measurable hr) hB hUn hBc he.
exists W; split=> //; split.
- apply: (@measure_null_subset R X phi hphi _ (A `\` B)) hz.
  move=> x [hx hnW]; split=> // hbx; apply: hnW; exact: hBW x hbx.
- have hBm := @borel_regular_borel_measurable R X psi hm hr B hB.
  have hi : W `&` B=B.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hBW x hx.
  rewrite (hBm W) hi hval.
  exact: leeD (lexx (psi B)) (ltW herr).
Qed.
