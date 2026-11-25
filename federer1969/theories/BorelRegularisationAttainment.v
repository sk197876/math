(** Federer (1969), 2.2.3, p. 62, final paragraph: regularisation by the
    infimum over Borel supersets. The construction is sealed; mathematical
    consequences use its greatest-lower-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import TopologicalBorel MeasureUP MeasureBasic
  BorelRegularisationUP BorelRegularisationBasic ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_regularisation_attained]: Federer 2.2.3, p. 62,
    supporting attainment of the Borel-superset infimum. A countable
    intersection of Borel supersets approaching the infimum attains it; for
    infinite value the whole space does. *)
Theorem borel_regularisation_attained (R : realType) (I : topologicalType)
    (mu nu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regularisation mu nu) A :
  exists B, A `<=` B /\ borel_set B /\ nu A = mu B.
Proof.
have hn := @borel_regularisation_nonnegative R I mu nu hm hr A.
case he: (nu A)=> [r| |].
- have happ : forall n, exists B, A `<=` B /\ borel_set B /\
      mu B < (r + ((n.+1)%:R)^-1)%:E.
    move=> n; apply: (@borel_regularisation_strict_approximation R I mu nu hr A).
    by rewrite he lte_fin ltrDl invr_gt0 ltr0n.
  pose C n := projT1 (cid (happ n)).
  have hC n : A `<=` C n /\ borel_set (C n) /\
      mu (C n) < (r + ((n.+1)%:R)^-1)%:E := projT2 (cid (happ n)).
  exists (\bigcap_n C n).
  have hAB : A `<=` \bigcap_n C n by move=> x hx n _; exact: (hC n).1.
  have hB : borel_set (\bigcap_n C n).
    apply: (@borel_set_countable_intersection I _ setT C (countableP _) (ex_intro _ 0%N Logic.I)).
    move=> n _; exact: (hC n).2.1.
  split=> //; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
  + rewrite -he; exact: (@borel_regularisation_lower R I mu nu hr A _ hAB hB).
  + apply: extended_real_reciprocal_upper_bound=> n.
    apply: le_trans (_ : mu (\bigcap_n C n) <= mu (C n)) (ltW (hC n).2.2).
    apply: (@measure_mono R I mu hm _ _)=> x hx; exact: (hx n Logic.I).
- exists setT; split; first by move=> x _.
  split; first exact: open_borel_set (@openT I).
  apply/eqP; rewrite eq_le leey andbT.
  have h := @borel_regularisation_lower R I mu nu hr A setT
    (fun x _ => Logic.I) (open_borel_set (@openT I)).
  by rewrite he in h.
- by move: hn; rewrite he.
Qed.
