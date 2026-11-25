(** Attainment for the measure introduced in Federer (1969), 2.9.1, p. 152,
    expanded from the elementary facts used in 2.9.2, p. 153. A countable
    intersection of nearly optimal Borel almost covers attains the infimum;
    no regularity beyond the two measure laws is needed. Source context:
    AbsoluteContinuousPartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartBasic
  MeasureUP MeasureBasic MeasureAlmostBasic TopologicalBorel ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_strict_approximation]: supporting infimum
    approximation for Federer 2.9.1, p. 152, used for the attainment
    assertion. The threshold is an arbitrary extended real strictly above
    the infimum. *)
Lemma continuous_part_strict_approximation (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_absolutely_continuous_part phi psi gamma -> forall A b,
  gamma A<b -> exists B, borel_set B /\ phi (A `\` B)=0 /\ psi B<b.
Proof.
move=> hg A b hb; apply: contrapT=> hn.
have hge : b<=gamma A.
  apply: (continuous_part_greatest hg)=> B hB hz.
  rewrite leNgt; apply/negP=> hlt; apply: hn; by exists B; split=> //; split.
by have := le_lt_trans hge hb; rewrite ltxx.
Qed.

(** Source for [continuous_part_attained]: supporting attainment of the
    infimum defining the measure in Federer 2.9.1, p. 152; used in 2.9.2, p.
    153. The countable intersection retains almost coverage because
    countably many phi-null exceptions are null. *)
Theorem continuous_part_attained (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  forall A, exists B, borel_set B /\ phi (A `\` B)=0 /\ gamma A=psi B.
Proof.
move=> hphi hpsi hg A.
have hn := @continuous_part_nonnegative R X phi psi gamma hpsi hg A.
case he: (gamma A)=> [r| |].
- have happ n : exists B, borel_set B /\ phi (A `\` B)=0 /\
      psi B<(r+((n.+1)%:R)^-1)%:E.
    apply: (@continuous_part_strict_approximation R X phi psi gamma hg A).
    by rewrite he lte_fin ltrDl invr_gt0 ltr0n.
  pose C n := projT1 (cid (happ n)).
  have hC n : borel_set (C n) /\ phi (A `\` C n)=0 /\
      psi (C n)<(r+((n.+1)%:R)^-1)%:E := projT2 (cid (happ n)).
  pose B := \bigcap_n C n.
  have hB : borel_set B.
    apply: (@borel_set_countable_intersection X nat setT C (countableP _) (ex_intro _ 0%N Logic.I)).
    by move=> n _; exact: (hC n).1.
  have hz : phi (A `\` B)=0.
    have hN : phi (\bigcup_n (A `\` C n))=0.
      apply: (@measure_null_countable_union R X nat phi hphi setT (fun n => A `\` C n) (countableP _)).
      by move=> n _; exact: (hC n).2.1.
    apply: (@measure_null_subset R X phi hphi _ _) hN.
    move=> x [hx hnB]; apply: contrapT=> hnU; apply: hnB=> n _.
    apply: contrapT=> hnC; apply: hnU; exists n=> //; by split.
  exists B; split=> //; split=> //; apply/eqP; rewrite eq_le; apply/andP; split.
  + rewrite -he; exact (@continuous_part_lower R X phi psi gamma hg A B hB hz).
  + apply: extended_real_reciprocal_upper_bound=> n.
    apply: le_trans (_ : psi B<=psi (C n)) (ltW (hC n).2.2).
    apply: (@measure_mono R X psi hpsi _ _)=> x hx; exact: hx n Logic.I.
- have hB : borel_set (@setT X) := open_borel_set openT.
  have hz : phi (A `\` setT)=0 by rewrite setDT (measure_empty hphi).
  exists setT; split=> //; split=> //; apply/eqP; rewrite eq_le leey andbT.
  have hb := @continuous_part_lower R X phi psi gamma hg A setT hB hz.
  by rewrite he in hb.
- by move: hn; rewrite he.
Qed.
