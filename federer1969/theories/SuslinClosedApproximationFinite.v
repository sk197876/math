(** Federer (1969), 2.2.12, pp. 68–69: closed inner approximation when the
    whole space has finite measure. The proof first regularises the measure,
    then uses the sealed coordinate pruning, compact-fiber identity, and
    continuity from above. No separation assumption on X is introduced. the
    Suslin theorem itself is not reproduced. Source context:
    RegularProjectionLoss.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SuslinSetUP MeasureUP MeasureBasic MeasureSplit
  MeasureRegularisation MeasureRegularisationBasic MeasurePruningUP MeasurePruningSealed
  PruningClosedProjectionLimit PruningClosedLimitMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [suslin_closed_approximation_finite_measure]: direct
    finite-total-measure case of Federer 2.2.12, pp. 68–69.
    The infimum regularisation dominates the original measure,
    agrees on closed measurable sets, and is regular. The closed
    limit lies in S by the compact-fiber argument; its complement
    in S has measure at most the requested tolerance. *)
Theorem suslin_closed_approximation_finite_measure (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X) (delta : R) :
  (forall C : set X, closed C -> measure_measurable mu C) ->
  mu setT < +oo -> is_suslin_set R S -> (0 < delta)%R ->
  exists C, closed C /\ C `<=` S /\ mu (S `\` C) <= delta%:E.
Proof.
move=> hclosed htotal [Z [hZ hZS]] hd.
pose gamma := measure_regularisation mu.
have hg : is_measure gamma := regularised_measure_is_measure hm.
have hgr := regularised_measure_regular hm.
have hgt : gamma setT < +oo.
  rewrite /gamma (regularised_measure_measurable_value hm (measure_measurable_whole hm)).
  exact htotal.
have hgc C : closed C -> measure_measurable gamma C.
  move=> hc; exact: (@regularised_measure_preserves_measurable R X mu hm C (hclosed C hc)).
pose choice := @MeasurePruning.value R X gamma hg hgr hgt delta hd Z.
have hchoice : is_measure_coordinate_pruning gamma Z delta choice.1 choice.2.
  exact: MeasurePruning.laws.
pose C := pruned_projection_closed_limit choice.2.
have hc : closed C := @pruned_projection_limit_closed R X choice.2.
have hCS : C `<=` S.
  rewrite -hZS; exact: pruned_projection_limit_within_original (measure_pruning_recursion hchoice) hZ.
have hl := @pruned_closed_limit_measure_lower_bound R X gamma hg Z delta choice.1 choice.2 hgc hgt hchoice.
rewrite hZS in hl.
have hCf : gamma C \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X gamma hg C).
  have hbound : gamma C <= gamma setT.
    apply: (@measure_mono R X gamma hg)=> x hx; exact Logic.I.
  exact: le_lt_trans hbound hgt.
have hi : S `&` C = C.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hCS x hx.
have hs := hgc C hc S.
rewrite hi in hs.
have herr : gamma (S `\` C) <= (delta / 2)%:E.
  move: hl; change (gamma S - (delta / 2)%:E <= gamma C -> gamma (S `\` C) <= (delta / 2)%:E).
  rewrite lee_subel_addr // hs leeD2lE //.
exists C; split=> //; split=> //.
apply: le_trans (@measure_regularisation_dominates R X mu gamma hm (measure_regularisation_laws mu) _) _.
apply: le_trans herr _; rewrite lee_fin.
rewrite ler_pdivrMr // ?ltr0n //.
by rewrite -{1}[delta]mulr1 ler_pM2l // ler1n.
Qed.
