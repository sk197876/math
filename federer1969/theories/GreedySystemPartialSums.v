(** Federer (1969), 2.3.3, p. 76: recover the scalar partial-sum recursion
    from the abstract characteristic and threshold laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import CharacteristicFunctionUP WeightedCharacteristicExpansionUP
  GreedyCharacteristicSystemUP GreedyScalarExpansionUP GreedyMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_system_partial_sum]: direct finite
    weighted characteristic sum appearing in the defining inequality
    of Federer 2.3.3, p. 76. *)
Definition greedy_system_partial_sum (R : realType) (X : Type)
    (r : nat -> R) (g : nat -> X -> R) n x := (\sum_(j < n) r j * g j x)%R.

(** Source for [greedy_system_set_identity]: direct threshold
    set identity in Federer 2.3.3, p. 76, now derived
    only from the abstract characteristic-system specification. *)
Lemma greedy_system_set_identity (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_greedy_characteristic_system f r A g -> forall n,
  A n = greedy_expansion_set r f (greedy_system_partial_sum r g) n.
Proof.
move=> hs n; apply/seteqP; split=> x hx.
- have h := (proj1 (greedy_system_threshold hs n x)) hx.
  by move: h; rewrite /greedy_expansion_set /greedy_system_partial_sum addrC.
- apply: (proj2 (greedy_system_threshold hs n x)).
  by move: hx; rewrite /greedy_expansion_set /greedy_system_partial_sum addrC.
Qed.

(** Source for [greedy_system_scalar_laws]: supporting recurrence
    recovered from the printed set formula of Federer 2.3.3,
    p. 76. No computation through the sealed system is used. *)
Lemma greedy_system_scalar_laws (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_greedy_characteristic_system f r A g -> forall x,
  is_greedy_scalar_expansion r (f x) (fun n => greedy_system_partial_sum r g n x).
Proof.
move=> hs x; constructor.
- by rewrite /greedy_system_partial_sum big_ord0.
- move=> n; rewrite /greedy_system_partial_sum big_ord_recr /=.
  case: ifP=> hc.
  + have ha : A n x.
      apply: (proj2 (greedy_system_threshold hs n x)).
      by rewrite addrC.
    by rewrite (characteristic_on_set (greedy_system_characteristic hs n) ha) mulr1.
  + have ha : ~ A n x.
      move=> ha; have h := (proj1 (greedy_system_threshold hs n x)) ha.
      rewrite addrC in h; by move/negP: hc; apply.
    by rewrite (characteristic_off_set (greedy_system_characteristic hs n) ha) mulr0 addr0.
Qed.

(** Source for [greedy_system_term_identity]: supporting selected term
    identity for the pointwise sum in Federer 2.3.3, p. 76 *)
Lemma greedy_system_term_identity (R : realType) (X : Type)
    (f : X -> \bar R) (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_greedy_characteristic_system f r A g -> forall n x,
  (r n * g n x)%R = greedy_scalar_term r (f x) (fun i => greedy_system_partial_sum r g i x) n.
Proof.
move=> hs n x; rewrite /greedy_scalar_term; case: ifP=> hc.
- have ha : A n x.
    rewrite (@greedy_system_set_identity R X f r A g hs n); exact hc.
  by rewrite (characteristic_on_set (greedy_system_characteristic hs n) ha) mulr1.
- have ha : ~ A n x.
    rewrite (@greedy_system_set_identity R X f r A g hs n).
    by move=> h; move/negP: hc; apply.
  by rewrite (characteristic_off_set (greedy_system_characteristic hs n) ha) mulr0.
Qed.
