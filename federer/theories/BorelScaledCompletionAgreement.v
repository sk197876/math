(** Federer (1969), 2.10.45, pp. 202–203: a finite positive multiple
    identity on Borel sets extends to every measurable set of the reference
    measure, using its finite Borel exhaustion. This is the completion step
    after Haar uniqueness, including infinite measure values. Source context
    and the Borel sandwich comparison: BorelMeasureCompletionAgreement.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP MeasureScaleIntegral
  BorelMeasureCompletionAgreement TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_scaled_agreement_completed_measure]: supporting
    extension of the Borel multiple identity in the last
    paragraph of 2.10.45, p. 203, to the full
    class of measurable U stated on p. 202.
    The reference is sigma finite through the supplied
    exhaustion; no regularity of the target is assumed. *)
Theorem borel_scaled_agreement_completed_measure (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure nu) (c : R) (E : nat -> set X) :
  (0<c)%R ->
  (forall B, borel_set B -> measure_measurable mu B) ->
  (forall B, borel_set B -> mu B=c%:E*nu B) ->
  (forall n, borel_set (E n)) -> (forall n, nu (E n)< +oo) ->
  (forall n m, (n<=m)%N -> E n `<=` E m) ->
  (forall x, exists n, E n x) -> forall A,
  measure_measurable nu A -> measure_measurable mu A /\ mu A=c%:E*nu A.
Proof.
move=> hc hb he hE hEf hEm hcov A hA.
pose ref := measure_scale c nu.
have href : is_measure ref := measure_scale_is_measure hn hc.
have hmeas B (hB : measure_measurable nu B) : measure_measurable ref B.
  exact (@measure_scale_measurable R X nu hn c B hB).
have hrref : is_borel_regular_measure ref.
  constructor.
  - move=> U hU; exact: hmeas U (borel_regular_open_measurable hr hU).
  - move=> B; have [D [hBD [hD hv]]] := borel_regular_cover hr B.
    exists D; split=> //; split=> //; by rewrite /ref /measure_scale hv.
have hfinite n : ref (E n)< +oo.
  have hf : nu (E n) \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hn (E n))).
  rewrite /ref /measure_scale -(fineK hf) -EFinM; exact: ltry.
exact (@borel_agreement_sigma_finite_completion R X mu ref hm href hrref E
  hb he hE hfinite hEm hcov A (hmeas A hA)).
Qed.
