(** Degenerate normal sections in Federer (1969), 2.10.30, p. 195. A
    nonempty null section becomes a singleton, whereas an empty section
    stays empty. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CenteredSectionUP CenteredSectionLaws LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_nonempty_null_section]: direct
    degenerate-segment case of 2.10.30, p. 195.
    Nonempty null sections collapse to the centre;
    they are not discarded. *)
Lemma centered_nonempty_null_section (R : realType) (A B : set (real_line_metric R)) :
  is_centered_section A B -> A !=set0 -> lebesgue_scalar_measure A=0%:E -> B=[set 0].
Proof.
move=> h hne hzero.
have [r [hr [hlen hm]]] := centered_section_membership h hne.
have hrad : r=0.
  rewrite hzero in hlen.
  have he : (0 : R)=r+r by move/eqP: hlen; rewrite eqe=> /eqP.
  lra.
apply/seteqP; split=> t.
- move/(hm t).1=> ht; rewrite hrad normr_le0 in ht; by move/eqP: ht.
- move=> ht; have ht0 : t=0 := ht.
  apply: (hm t).2; by rewrite ht0 hrad normr0.
Qed.
