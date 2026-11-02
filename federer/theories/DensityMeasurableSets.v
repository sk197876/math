(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureHull MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext MeasureDensityPoints
  DerivationBorelHulls DensityHullAgreement MeasurableExtendedGraphLevel HullSetAgreementConsequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_one_points_conclusions]: direct P half of Federer
    2.9.11, p. 158 P is measurable, contains almost all of A, A union P is a
    hull of A, and A is measurable precisely when P minus A is null. No
    measurability of A is imposed in advance. *)
Theorem density_one_points_conclusions (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context phi V ->
  measure_measurable phi (measure_density_one_points phi V A) /\
  phi (A `\` measure_density_one_points phi V A)=0 /\
  is_measure_hull phi A (A `|` measure_density_one_points phi V A) /\
  (measure_measurable phi A <-> phi (measure_density_one_points phi V A `\` A)=0).
Proof.
move=> hc; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
have hDm := @measurable_set_restriction_derivate R X phi V A hc.
have hPm := @measurable_extended_graph_level R X phi _ 1 hm hDm.
have [B [_ hB]] := @derivation_measure_borel_hull R X phi A hphi.
have hPA := @density_one_points_hull_agreement R X phi V A B hc hB.
split; first exact hPm.
exact (@hull_set_agreement_consequences R X phi A B (measure_density_one_points phi V A) hm hB hPm hPA).
Qed.

(** Source for [density_complement_zero_points_conclusions]: direct Q half
    of Federer 2.9.11, p. 158 Apply the same hull reasoning to X minus A and
    X minus Q. The two set-complement identities give the printed hull X
    minus (A intersection Q) and the second measurability criterion exactly. *)
Theorem density_complement_zero_points_conclusions (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context phi V ->
  measure_measurable phi (measure_density_complement_zero_points phi V A) /\
  phi (measure_density_complement_zero_points phi V A `\` A)=0 /\
  is_measure_hull phi (~` A) (~` (A `&` measure_density_complement_zero_points phi V A)) /\
  (measure_measurable phi A <-> phi (A `\` measure_density_complement_zero_points phi V A)=0).
Proof.
move=> hc; have hphi := derivation_context_measure hc.
have hm := derivation_measure_law hphi.
pose Q := measure_density_complement_zero_points phi V A.
have hDm := @measurable_set_restriction_derivate R X phi V (~` A) hc.
have hQm : measure_measurable phi Q := @measurable_extended_graph_level R X phi _ 0 hm hDm.
have hRm := @measure_measurable_complement R X phi Q hQm.
have [C [_ hC]] := @derivation_measure_borel_hull R X phi (~` A) hphi.
have hQC := @density_complement_zero_points_hull_agreement R X phi V A C hc hC.
have hRC : measure_almost_everywhere phi [set x | (~` Q) x <-> C x].
  apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hQC)=> x hx; split.
  - move=> hnq; apply: contrapT=> hnc; exact: hnq (hx.2 hnc).
  - by move=> hxC hq; exact: (hx.1 hq) hxC.
have [hnull [hhull hiff]] := @hull_set_agreement_consequences R X phi (~` A) C (~` Q) hm hC hRm hRC.
have he1 : (~` A) `\` (~` Q)=Q `\` A by rewrite !setDE setCK setIC.
have he2 : (~` Q) `\` (~` A)=A `\` Q by rewrite !setDE setCK setIC.
have he3 : (~` A) `|` (~` Q)=~` (A `&` Q) by rewrite setCI.
rewrite he1 in hnull; rewrite he3 in hhull; rewrite he2 in hiff.
split=> //; split=> //; split=> //; split.
- move=> hA; exact: hiff.1 (@measure_measurable_complement R X phi A hA).
- move=> h; have hAc := hiff.2 h.
  have ha := @measure_measurable_complement R X phi (~` A) hAc.
  by rewrite setCK in ha.
Qed.

(** Source for [federer_2_9_11]: direct complete theorem Federer 2.9.11, p.
    158. The two groups give all assertions about P and Q, including both
    original measurability equivalences and the exact hull sets. that
    additional assertion is not needed for the numbered Federer theorem. *)
Theorem federer_2_9_11 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop) (A : set X) :
  is_measure_derivation_context phi V ->
  (measure_measurable phi (measure_density_one_points phi V A) /\
    phi (A `\` measure_density_one_points phi V A)=0 /\
    is_measure_hull phi A (A `|` measure_density_one_points phi V A) /\
    (measure_measurable phi A <-> phi (measure_density_one_points phi V A `\` A)=0)) /\
  (measure_measurable phi (measure_density_complement_zero_points phi V A) /\
    phi (measure_density_complement_zero_points phi V A `\` A)=0 /\
    is_measure_hull phi (~` A) (~` (A `&` measure_density_complement_zero_points phi V A)) /\
    (measure_measurable phi A <-> phi (A `\` measure_density_complement_zero_points phi V A)=0)).
Proof.
move=> hc; split.
- exact: density_one_points_conclusions hc.
- exact: density_complement_zero_points_conclusions hc.
Qed.
