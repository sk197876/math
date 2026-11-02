(** Federer (1969), 2.9.18(2), p. 163: the image measure of sets after
    removing the supporting straight line. This is an outer measure, without
    a Borel-regularity assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [image_complement_measure]: direct formula
    psi(A)=L^1[p(A minus T)] in Federer 2.9.18(2),
    p. 163, with arbitrary image map and
    target measure for the supporting measure-law proof. *)
Definition image_complement_measure (R : realType) (X Y : choiceType)
    (mu : set Y -> \bar R) (p : X -> Y) (T A : set X) := mu (p @` (A `\` T)).

(** Source for [image_complement_measure_is_measure]: direct
    assertion that psi in Federer 2.9.18(2), p. 163,
    measures the ambient space. Images of a cover cover
    the image of the target after removing T, so the
    existing indexed covering inequality gives the result.
    No injectivity or measurability of p is required. *)
Theorem image_complement_measure_is_measure (R : realType) (X Y : choiceType)
    (mu : set Y -> \bar R) (p : X -> Y) (T : set X) :
  is_measure mu -> is_measure (image_complement_measure mu p T).
Proof.
move=> hm; constructor; first by move=> A; exact (@measure_nonnegative R Y mu hm _).
move=> A F hF hcover.
apply: (@measure_indexed_cover R Y [the choiceType of set X] mu hm
  (p @` (A `\` T)) F (fun B => p @` (B `\` T)) hF).
move=> y [x [hx hn] <-]; have [B hB hxB] := hcover x hx.
exists B=> //; exists x=> //; by split.
Qed.

(** Source for [image_complement_measure_target_null]: direct
    psi(T)=0 in Federer 2.9.18(2), p. 163.
    Removing T leaves the empty set and its image is empty. *)
Lemma image_complement_measure_target_null (R : realType) (X Y : choiceType)
    (mu : set Y -> \bar R) (p : X -> Y) (T : set X) :
  is_measure mu -> image_complement_measure mu p T T=0.
Proof. by move=> hm; rewrite /image_complement_measure setDv image_set0; exact: measure_empty hm. Qed.
