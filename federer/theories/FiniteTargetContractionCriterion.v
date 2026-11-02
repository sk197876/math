(** Federer (1969), proof of 2.8.2, pp. 142–143: the case in which every
    target has finite measure. The recurrent enumeration and the
    finite-selection exhaustion are used only through their sealed laws.
    Source context: ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP CoveringFamilyUP CoveringFamilyLaws
  RecurrentEnumerationUP RecurrentEnumeration ContractionCoverUP
  CoverContractionExhaustion ContractionExhaustionLaws ContractionExhaustionAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_target_contraction_adequacy]: the
    finite-target-measure case of Federer 2.8.2, pp. 142–143. The auxiliary
    scalar function is total on the ambient set type, but its values and
    laws are used only for members of K. The final book statement can
    therefore take its scalar function on K itself. The target sets need not
    be measurable. *)
Theorem finite_target_contraction_adequacy (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F K : set (set X)) (sigma : set X -> R) :
  (forall B, F B -> closed B) ->
  (forall U, open U -> measure_measurable mu U) -> countable K ->
  (forall T, K T -> mu T < +oo) ->
  (forall T, K T -> (0 < sigma T < 1)%R) ->
  (forall T, K T -> has_local_cover_contraction mu F T (sigma T)) ->
  family_is_measure_adequate mu F (\bigcup_(T in K) T).
Proof.
move=> hF hopen hK hfinite hsigma hlocal.
case: (pselect (exists T, K T))=> [hKn|hKe].
- pose b := @recurrent_enumeration [the choiceType of set X] K hK hKn.
  have hb : is_recurrent_enumeration K b.
    exact: recurrent_enumeration_specification.
  have hmember n : K (b n) := @recurrent_enumeration_members [the choiceType of set X] K b hb n.
  have hf n : mu (b n) < +oo := hfinite (b n) (hmember n).
  have hs n : (0 < sigma (b n) < 1)%R := hsigma (b n) (hmember n).
  have hl n : has_local_cover_contraction mu F (b n) (sigma (b n)).
    exact: hlocal (b n) (hmember n).
  move=> V hV.
  pose p := @cover_contraction_exhaustion R X mu hm F b (fun n => sigma (b n))
    hF hopen hf hs hl V hV.
  have hE : is_cover_contraction_exhaustion mu F b
      (fun n => Num.sqrt (sigma (b n))) V p.1 p.2.
    exact: cover_contraction_exhaustion_specification.
  exists (cover_exhaustion_family p.2).
  exact (@contraction_exhaustion_adequate_selection R X mu hm F K sigma b V p.1 p.2
    hK hb hfinite hsigma hE).
- have he : (\bigcup_(T in K) T) = set0.
    apply/seteqP; split=> [x [T hT _]|x []].
    exfalso; apply: hKe; by exists T.
  rewrite he; exact (@adequate_family_empty_target R X mu hm F).
Qed.
