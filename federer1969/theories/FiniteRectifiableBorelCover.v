(** Federer (1969), 3.2.32, pp. 269–270: supporting
    Borel covers of finite measurable rectifiable thresholds.
    The Borel sandwich 2.2.3, p. 61, supplies a proved
    null difference before rectifiability is transferred. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureNullModification
  BorelRegularMeasureUP BorelRegularSandwich TopologicalBorel RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measurable_rectifiable_borel_cover_exists]:
    supporting Borel target pieces in Federer 3.2.32, p. 270.
    A finite measurable rectifiable set has a finite rectifiable
    Borel superset with null difference and equal mass. The
    measurability hypothesis is used by the Borel sandwich;
    no null-difference assertion is made for a nonmeasurable set. *)
Theorem finite_measurable_rectifiable_borel_cover_exists (R:realType) (X:metricType R)
    (beta:set X->\bar R) (hb:is_measure beta) (hr:is_borel_regular_measure beta) mu (Z:set X):
  measure_measurable beta Z ->is_measure_m_rectifiable beta mu Z ->
  exists B,borel_set B /\is_measure_m_rectifiable beta mu B /\Z `<=` B /\beta (B `\` Z)=0.
Proof.
move=>hZ hRect.
have [A [B [hA [hB [hAZ [hZB hNull]]]]]]:=@borel_regular_finite_sandwich R X beta hb hr Z hZ hRect.2.
have hDiff:beta (B `\` Z)=0.
  apply:(measure_null_subset hb _ hNull)=>x [hx hNot]; split=>//.
  move=>hAx; exact:hNot (hAZ x hAx).
have hMass:beta B=beta Z.
  apply:(measure_null_modification_value hb hDiff)=>x hNot.
  split.
  - move=>hBx; case:(pselect (Z x))=>hZx; first exact hZx.
    exfalso; apply:hNot; by split.
  - exact:hZB.
have hRectB:is_measure_m_rectifiable beta mu B.
  split; last by rewrite hMass; exact hRect.2.
  split; first exact hb.
  have [_ [C [hC hZC]]]:=hRect.1.
  exists C; split; first exact hC.
  have hUnion:beta ((Z `\` C) `|` (B `\` Z))=0:=measure_null_union hb hZC hDiff.
  apply:(measure_null_subset hb _ hUnion)=>x [hBx hNotC].
  case:(pselect (Z x))=>hZx; [left|right]; by split.
exists B; split=>//; split=>//; by split.
Qed.
