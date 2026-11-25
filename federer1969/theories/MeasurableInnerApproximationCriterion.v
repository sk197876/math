(** Federer (1969), 2.2.12, p. 68: the closed-inner- approximation assertion
    implies measurability of the Suslin set. We expand this implication
    using the finite-test criterion in 2.1.2, p. 54. Measurable inner
    approximants suffice; the supporting lemma therefore does not require
    topology. It does not reproduce the Suslin theorem. Source context:
    SequenceBoxes.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_inner_approximation_criterion]: supporting
    justification of "Therefore S is ... measurable" in Federer
    2.2.12, p. 68, paraphrased without the measure symbol.
    Every finite test set admits a measurable inner approximant
    with arbitrarily small residual measure. The finite-test
    splitting inequality follows by sending that error to zero. *)
Theorem measurable_inner_approximation_criterion (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (S : set I) :
  (forall T, mu T < +oo -> forall epsilon : R, (0 < epsilon)%R ->
    exists C, measure_measurable mu C /\ C `<=` S /\
      mu ((T `&` S) `\` C) <= epsilon%:E) ->
  measure_measurable mu S.
Proof.
move=> happ; apply: (proj2 (@measure_measurable_finite_test R I mu hm S))=> T hf.
have hfin : mu T \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R I mu hm T).
rewrite -(fineK hfin); apply: extended_real_reciprocal_upper_bound=> n.
pose e := (((n.+1)%:R : R)^-1)%R.
have he : (0 < e)%R by rewrite /e invr_gt0 ltr0n.
have [C [hC [hCS herr]]] := happ T hf e he.
have hcover : T `&` S `<=` (T `&` C) `|` ((T `&` S) `\` C).
  move=> x [ht hs]; case: (pselect (C x))=> hc.
  - left; by split.
  - right; by split; first split.
have hb : mu (T `&` S) <= mu (T `&` C) + e%:E.
  apply: le_trans (@measure_binary_cover R I mu hm _ _ _ hcover) _.
  exact: leeD (lexx _) herr.
have hr : mu (T `\` S) <= mu (T `\` C).
  apply: (@measure_mono R I mu hm)=> x [hx hs]; split=> // hc; exact: hs (hCS x hc).
have h := leeD hb hr.
rewrite addeAC -(hC T) -(fineK hfin) -EFinD in h.
exact h.
Qed.
