(** Public scalar Lebesgue measure used in Federer (1969), 2.6.5, pp.
    119–120. Only the sealed characterising laws of 2.5.17, p. 111, are
    used. The countable segment cover makes the hypotheses of the corrected
    associativity theorem explicit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground LebesgueLineUP LebesgueLineSealed
  MeasureUP BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_scalar_measure]: L^1 in Federer
    2.5.17, p. 111, and the scalar factor of 2.6.5,
    pp. 119–120, exposed through its abstract characterisation. *)
Definition lebesgue_scalar_measure (R : realType) := @LebesgueLine.value R.

(** Source for [lebesgue_scalar_specification]: defining
    laws of Federer 2.5.17, p. 111, for 2.6.5. *)
Lemma lebesgue_scalar_specification (R : realType) :
  is_lebesgue_line_measure (@lebesgue_scalar_measure R).
Proof. exact: LebesgueLine.laws. Qed.

(** Source for [lebesgue_scalar_is_measure]: measure law
    for L^1, Federer 2.5.17, p. 111. *)
Lemma lebesgue_scalar_is_measure (R : realType) : is_measure (@lebesgue_scalar_measure R).
Proof. exact: lebesgue_line_measure_law (lebesgue_scalar_specification R). Qed.

(** Source for [lebesgue_scalar_borel_regular]: Borel
    regularity of L^1, Federer 2.5.17, p. 111,
    used explicitly in 2.6.5, p. 120. *)
Lemma lebesgue_scalar_borel_regular (R : realType) : is_borel_regular_measure (@lebesgue_scalar_measure R).
Proof. exact: lebesgue_line_borel_law (lebesgue_scalar_specification R). Qed.

(** Source for [lebesgue_scalar_segment]: segment length
    formula of Federer 2.5.17, p. 111. *)
Lemma lebesgue_scalar_segment (R : realType) (a b : R) :
  a <= b -> lebesgue_scalar_measure `[a,b] = (b-a)%:E.
Proof. exact (@lebesgue_line_segment_law R (@lebesgue_scalar_measure R) (lebesgue_scalar_specification R) a b). Qed.

(** Source for [lebesgue_scalar_singleton]: singleton
    nullity supporting the polynomial base case in Federer
    2.6.5, p. 120, by the degenerate segment formula
    already proved for 2.5.17, p. 111. *)
Lemma lebesgue_scalar_singleton (R : realType) (x : R) :
  lebesgue_scalar_measure [set x] = 0%:E.
Proof.
have he : [set x] = `[x,x].
  apply/seteqP; split=> y.
  - by move=> <-; rewrite /= in_itv /= lexx.
  - rewrite /= in_itv /= => /andP[hxy hyx]; apply/eqP; by rewrite eq_le hxy hyx.
by rewrite he lebesgue_scalar_segment ?lexx // subrr.
Qed.

(** Source for [lebesgue_scalar_countably_measurable]: the countable
    finite-measure cover needed for the corrected product associations in
    Federer 2.6.5, pp. 119–120 Closed segments [-n,n] cover the line and
    have finite measure. *)
Lemma lebesgue_scalar_countably_measurable (R : realType) :
  measure_countably_measurable (@lebesgue_scalar_measure R) setT.
Proof.
apply/(countably_measurable_sequence_iff (lebesgue_scalar_is_measure R)).
exists (fun n : nat => `[- n%:R, n%:R]); split.
- apply/seteqP; split=> x _; last exact Logic.I.
  have /andP[_ hx] := truncn_itv (normr_ge0 x).
  exists (Num.truncn `|x|).+1=> //.
  rewrite /= in_itv /= -ler_norml; exact: ltW hx.
- move=> n; split.
  + apply: (borel_regular_borel_measurable (lebesgue_scalar_is_measure R)
      (lebesgue_scalar_borel_regular R)).
    apply: closed_borel_set; exact: segment_closed_real.
  + rewrite lebesgue_scalar_segment; first exact: ltry.
    have hn : - n%:R <= (0 : R) by rewrite oppr_le0 ler0n.
    exact: le_trans hn (ler0n R n).
Qed.
