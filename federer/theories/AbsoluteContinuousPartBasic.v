(** Consequences of the infimum in Federer (1969), 2.9.1, p. 152, in
    particular the printed inequality psi_phi <= psi. The laws below use
    only the abstract specification. Measure and decomposition assertions of
    2.9.2, p. 153, are separate. Source context: AbsoluteContinuousPartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureSplit BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_nonnegative]: supporting
    nonnegativity of the infimum in Federer 2.9.1,
    p. 152. This only requires nonnegative values
    of the numerator measure, not any selection or derivative. *)
Lemma continuous_part_nonnegative (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure psi -> is_absolutely_continuous_part phi psi gamma -> forall A, 0<=gamma A.
Proof.
move=> hm hg A; apply: (continuous_part_greatest hg)=> B _ _; exact (@measure_nonnegative R X psi hm B).
Qed.

(** Source for [continuous_part_monotone]: supporting
    monotonicity of the infimum in Federer 2.9.1,
    p. 152. An almost Borel cover of a
    larger set also covers a smaller set up to a null set. *)
Lemma continuous_part_monotone (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_absolutely_continuous_part phi psi gamma ->
  forall A C, A `<=` C -> gamma A<=gamma C.
Proof.
move=> hm hg A C hAC; apply: (continuous_part_greatest hg)=> B hB hz.
apply: (@continuous_part_lower R X phi psi gamma hg A B hB).
apply: (@measure_null_subset R X phi hm _ (C `\` B)) hz.
by move=> x [hx hn]; split=> //; exact: hAC x hx.
Qed.

(** Source for [continuous_part_dominated]: direct proof of the final
    observation in Federer 2.9.1, p. 152 (paraphrase: the associated value
    is bounded above by the numerator measure) A Borel hull of A for psi is
    an eligible almost cover for phi. *)
Lemma continuous_part_dominated (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_borel_regular_measure psi ->
  is_absolutely_continuous_part phi psi gamma -> forall A, gamma A<=psi A.
Proof.
move=> hm hr hg A; have [B [hAB [hB he]]] := borel_regular_cover hr A.
rewrite he; apply: (@continuous_part_lower R X phi psi gamma hg A B hB).
have -> : A `\` B=set0.
  apply/seteqP; split=> [x [hx hn]|x []]; exfalso; exact: hn (hAB x hx).
exact: measure_empty hm.
Qed.

(** Source for [continuous_part_null]: supporting zero
    value on phi-null sets for the operator introduced in
    Federer 2.9.1, p. 152. This foreshadows the
    absolute continuity conclusion of 2.9.2, p. 153,
    without assuming the operator is already a measure. *)
Lemma continuous_part_null (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure psi -> is_absolutely_continuous_part phi psi gamma ->
  forall A, phi A=0 -> gamma A=0.
Proof.
move=> hm hg A hz; apply/eqP; rewrite eq_le (continuous_part_nonnegative hm hg A) andbT.
rewrite -(measure_empty hm).
apply: (@continuous_part_lower R X phi psi gamma hg A set0 (@open_borel_set X set0 open0)).
by rewrite setD0.
Qed.
