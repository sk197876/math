(** Federer (1969), 2.5.10, p. 101, last paragraph: the support of the
    measure restricted to a positive compact remainder is an eligible new
    compact piece. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureRestrictionSupport
  MeasureSupportUP MeasureSupport RadonMeasureUP RadonBorelRegularity RadonSupport
  RadonCompactRestriction MeasureNullModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_positive_compact_piece]: the eligible compact sets K in
    Federer 2.5.10, p. 101, paraphrased: every open set meeting K has
    positive measure on K. The empty compact set is eligible. *)
Definition is_positive_compact_piece (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (K : set T) :=
  compact K /\ forall V, open V -> K `&` V <> set0 -> 0 < mu (K `&` V).

(** Source for [compact_restriction_support_within]: the inclusion Z within
    Y in Federer 2.5.10, p. 101. The complement of Y is open and null for
    the restricted measure. *)
Lemma compact_restriction_support_within (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (Y : set T) :
  compact Y -> measure_support (measure_restrict mu Y) `<=` Y.
Proof.
move=> hY x hx; apply: contrapT=> hn.
have hs := proj1 (measure_support_neighborhood_law
  (measure_support_specification (measure_restrict mu Y)) x) hx.
have ho := closed_openC (compact_closed (radon_hausdorff hr) hY).
apply: (hs (~` Y) ho hn); exact: (@measure_restrict_outside_null R T mu hm Y (~` Y) (fun x hx => hx)).
Qed.

(** Source for [compact_restriction_support_piece]: eligibility of Z in
    Federer 2.5.10, p. 101 *)
Lemma compact_restriction_support_piece (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (Y : set T) :
  compact Y -> is_positive_compact_piece mu (measure_support (measure_restrict mu Y)).
Proof.
move=> hY; pose nu := measure_restrict mu Y; pose Z := measure_support nu.
have hn := measure_restrict_is_measure hm Y.
have hnr := radon_measure_compact_restriction hm hr hY.
have hZY := compact_restriction_support_within hm hr hY.
have hnull : mu (Y `\` Z)=0 := radon_support_complement_null hn hnr.
split.
- have he : Y `&` Z=Z.
    apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: hZY.
  have hh := @compact_closedI T Y Z hY (@measure_support_closed R T nu).
  by rewrite he in hh.
- move=> V hV hne.
  have [x [hx hv]] : exists x, (Z `&` V) x.
    apply: contrapT=> h; apply: hne; apply/seteqP; split=> [x hx|x []].
    apply: h; by exists x.
  have hp := proj1 (measure_support_neighborhood_law (measure_support_specification nu) x) hx V hV hv.
  have he : mu (Z `&` V)=nu V.
    apply: (@measure_null_modification_value R T mu hm _ _ (Y `\` Z) hnull)=> y hy.
    split=> [[hz hv']|[hY' hv']].
    + split=> //; exact: hZY.
    + split=> //; apply: contrapT=> hz; apply: hy; by split.
  rewrite he lt_neqAle (measure_nonnegative hn) andbT.
  apply/eqP=> heq; apply: hp; exact: esym heq.
Qed.

(** Source for [positive_compact_restriction_support_nonempty]: Z is
    nonempty in Federer 2.5.10, p. 101 Otherwise the Radon support theorem
    would force the positive compact remainder to have zero measure. *)
Lemma positive_compact_restriction_support_nonempty (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) (Y : set T) :
  compact Y -> 0 < mu Y -> measure_support (measure_restrict mu Y) <> set0.
Proof.
move=> hY hp he.
have hh := radon_support_complement_null (measure_restrict_is_measure hm Y)
  (radon_measure_compact_restriction hm hr hY).
rewrite he setC0 /measure_restrict setIT in hh.
by rewrite hh ltxx in hp.
Qed.
