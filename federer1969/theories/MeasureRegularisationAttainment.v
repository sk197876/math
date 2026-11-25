(** Federer (1969), 2.1.5, p. 57, regularisation by measurable supersets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureCountableClosure
  MeasureRegularisationUP MeasureRegularisationBasic ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_regularisation_attained]: Federer 2.1.5, p. 57,
    supporting attainment of the displayed infimum by an originally
    measurable superset. The infinite case uses X. *)
Theorem measure_regularisation_attained (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_measure_regularisation mu nu) A :
  exists B, A `<=` B /\ measure_measurable mu B /\ nu A = mu B.
Proof.
have hn := @measure_regularisation_nonnegative R I mu nu hm hr A.
case he: (nu A)=> [r| |].
- have happ : forall n, exists B, A `<=` B /\ measure_measurable mu B /\
      mu B < (r + ((n.+1)%:R)^-1)%:E.
    move=> n; apply: (@measure_regularisation_strict_approximation R I mu nu hr A).
    by rewrite he lte_fin ltrDl invr_gt0 ltr0n.
  pose C n := projT1 (cid (happ n)).
  have hC n : A `<=` C n /\ measure_measurable mu (C n) /\
      mu (C n) < (r + ((n.+1)%:R)^-1)%:E := projT2 (cid (happ n)).
  exists (\bigcap_n C n).
  have hAB : A `<=` \bigcap_n C n by move=> x hx n _; exact: (hC n).1.
  have hB : measure_measurable mu (\bigcap_n C n).
    apply: (@measure_measurable_countable_intersection R I _ mu hm setT C (countableP _)).
    move=> n _; exact: (hC n).2.1.
  split=> //; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
  + rewrite -he; exact: (@measure_regularisation_lower R I mu nu hr A _ hAB hB).
  + apply: extended_real_reciprocal_upper_bound=> n.
    apply: le_trans (_ : mu (\bigcap_n C n) <= mu (C n)) (ltW (hC n).2.2).
    apply: (@measure_mono R I mu hm _ _)=> x hx; exact: (hx n Logic.I).
- exists setT; split; first by move=> x _.
  split; first exact: measure_measurable_whole hm.
  apply/eqP; rewrite eq_le leey andbT.
  have h := @measure_regularisation_lower R I mu nu hr A setT
    (fun x _ => Logic.I) (measure_measurable_whole hm).
  by rewrite he in h.
- by move: hn; rewrite he.
Qed.
