(** Federer (1969), 2.5.10, p. 101: the class of finite-measure closed sets
    suffices for the decomposition of a Borel regular measure on a separable
    metric space, by 2.2.3, pp. 61–62. it does not state the CH conclusion.
    The approximation lemma below itself needs no separability or CH. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology pseudometric_structure.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic BorelRegularMeasureUP BorelRegularApproximation
  ClosedApproximationUP ExtendedRealReciprocalBounds FiniteMeasureDecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_closed_measure_family]: the class C in
    Federer 2.5.10, p. 101: all closed sets of finite
    measure. This is a predicate on sets, independent of a chosen order. *)
Definition finite_closed_measure_family (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) := [set K | closed K /\ mu K < +oo].

(** Source for [borel_regular_finite_closed_countable_cover]: supporting use
    of 2.2.3 in Federer 2.5.10, p. 101 A Borel hull followed by closed inner
    approximations almost covers every finite-measure test set, even when
    that original set is not measurable. *)
Lemma borel_regular_finite_closed_countable_cover (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu) :
  finite_measure_sets_countably_covered mu (finite_closed_measure_family mu) (fun K => K).
Proof.
move=> A hfin; have [B [hAB [hB he]]] := borel_regular_cover hr A.
have hBm := borel_regular_borel_measurable hm hr hB.
have hBfin : mu B < +oo by rewrite -he.
have hex n : exists K, closed K /\ K `<=` B /\ mu (B `\` K) < (((n.+1)%:R : R)^-1)%:E.
  apply: (@borel_regular_closed_approximation R T mu hm hr B hBm hBfin).
  by rewrite invr_gt0 ltr0n.
pose K n := projT1 (cid (hex n)); have hK n := projT2 (cid (hex n)).
exists (K @` setT); split.
- move=> L [n _ <-]; split; first exact: (hK n).1.
  apply: le_lt_trans _ hBfin; exact: (@measure_mono R T mu hm _ _ (hK n).2.1).
- split.
  + apply: sub_countable (card_image_le _ _) _; exact: countableP.
  + apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
    apply: (@extended_real_reciprocal_upper_bound R _ 0)=> n; rewrite add0r.
    apply: le_trans _ (ltW (hK n).2.2).
    apply: (@measure_mono R T mu hm)=> x [hx hn]; split; first exact: hAB.
    move=> hk; apply: hn; exists (K n)=> //; by exists n.
Qed.
