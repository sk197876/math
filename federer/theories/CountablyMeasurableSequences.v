(** Federer (1969), 2.3.4, p. 76: equivalence of countable-family and
    sequence formulations. Empty and finite families are included, using
    empty padding when the family itself is empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit CountablyMeasurableUP CountableFamilyEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_sequence_iff]: supporting equivalence
    of the printed family formulation in Federer 2.3.4, p. 76. Every term of
    the sequence is measurable and finite. *)
Theorem countably_measurable_sequence_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) :
  measure_countably_measurable mu A <-> exists F : nat -> set X,
    A = \bigcup_n F n /\ forall n, measure_measurable mu (F n) /\ mu (F n) < +oo.
Proof.
split.
- move=> [C [hc [he hC]]]; case: (pselect (C !=set0))=> [hn|hn].
  + have [F hF] := @countable_nonempty_family_enumeration X [the choiceType of set X]
      C (fun B => B) hc hn.
    have hFC n : C (F n).
      have hmem : (F @` setT) (F n) by exists n.
      rewrite hF in hmem; have [B hB eB] := hmem; by rewrite -eB.
    exists F; split.
    * rewrite he; apply/seteqP; split=> x.
      -- move=> [B hB hx]; have hmem : ((fun B => B) @` C) B by exists B.
         rewrite -hF in hmem; have [n _ en] := hmem.
         exists n=> //; by rewrite en.
      -- move=> [n _ hx]; exists (F n)=> //; exact: hFC n.
    * move=> n; exact: hC _ (hFC n).
  + have hA : A = set0.
      rewrite he; apply/seteqP; split=> x; last by [].
      move=> [B hB _]; apply: hn; by exists B.
    exists (fun _ => set0); split.
    * rewrite hA; apply/seteqP; split=> x; [by []|by move=> [n _ []]].
    * move=> n; split; first exact: measure_measurable_empty hm.
      rewrite (measure_empty hm); exact: ltry.
- move=> [F [he hF]]; exists (F @` setT); split.
  + apply: sub_countable (card_image_le _ _) _; exact: countableP.
  + split.
    * rewrite he; apply/seteqP; split=> x.
      -- move=> [n _ hx]; exists (F n)=> //; by exists n.
      -- move=> [B [n _ <-] hx]; by exists n.
    * by move=> B [n _ <-]; exact: hF n.
Qed.
