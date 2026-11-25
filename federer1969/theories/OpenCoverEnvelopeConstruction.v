(** Private existence proof for Federer (1969), 2.5.14, pp. 107–108: extend
    a countably subadditive open cost by its outer infimum. We reduce it to
    the project's proved countable-cover envelope by giving nonopen
    generators infinite cost; the resulting infimum is proved to satisfy
    exactly the open-envelope laws. No external measure construction is
    imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import OpenCoverContentUP NonnegativeSum NonnegativeSumSupport
  CountableCoverEnvelopeUP CountableCoverEnvelopeBasic CountableCoverEnvelopeLaws
  CountableCoverEnvelopeSealed MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_cover_generator_cost]: private supporting cost for the
    construction of Phi in Federer 2.5.14, pp. 107–108 Infinite cost
    excludes nonopen generators from finite covers. *)
Definition open_cover_generator_cost (R : realType) (X : topologicalType)
    (a : set X -> \bar R) V := if pselect (open V) is left _ then a V else +oo.

(** Source for [open_cover_envelope_exists]: the measure assertion in
    Federer 2.5.14, p. 108, from the open-cost assumptions isolated. The
    abstract conclusion retains all subsets and infinite values. *)
Theorem open_cover_envelope_exists (R : realType) (X : topologicalType)
    (a : set X -> \bar R) : is_open_cover_content a ->
  exists nu, is_open_cover_envelope a nu /\ is_measure nu.
Proof.
move=> ha; pose cost := @open_cover_generator_cost R X a.
have hcost V : 0 <= cost V.
  rewrite /cost /open_cover_generator_cost; case: pselect=> hV; last exact: leey.
  exact: (@open_cover_content_nonnegative R X a ha V hV).
have hcostE V : open V -> cost V=a V.
  move=> hV; rewrite /cost /open_cover_generator_cost; by case: pselect.
pose nu := @CountableCoverEnvelope.value R X [the choiceType of set X] id cost.
have hn := @CountableCoverEnvelope.laws R X [the choiceType of set X] id cost.
have hm : is_measure nu := countable_cover_envelope_is_measure hn hcost.
exists nu; split=> //; constructor.
- move=> S V hV hSV.
  apply: le_trans (@measure_mono R X nu hm S V hSV) _.
  have hb := @countable_cover_envelope_generator_bound R X [the choiceType of set X] id cost nu hn V (hcost V).
  by rewrite hcostE in hb.
- move=> S b hb; apply: (countable_cover_envelope_greatest hn)=> G hc hSG.
  case: (pselect (exists V, G V /\ ~ open V))=> [[V [hVG hV]]|hnone].
  + have he : cost V=+oo by rewrite /cost /open_cover_generator_cost; case: pselect.
    apply: le_trans (leey b) _; rewrite -he; exact: (@nonnegative_sum_term R [the choiceType of set X] G cost V hVG).
  + have ho V : G V -> open V.
      move=> hV; apply: contrapT=> hnV; apply: hnone; exists V; by split.
    have hoW : open (\bigcup_(V in G) V) by apply: bigcup_open.
    have hle := hb _ hoW hSG.
    have hsub : (\bigcup_(V in G) V) `<=` (\bigcup_(V in G) V) by [].
    have hcover := @open_cover_content_cover R X a ha _ G hoW hc ho hsub.
    apply: le_trans hle _; apply: le_trans hcover _; apply: nonnegative_sum_mono=> V hV.
    by rewrite hcostE //; exact: ho hV.
Qed.
