(** Finite counting adapter supporting the local counterexample in Federer
    (1969), 2.3.8, p. 78, from the counting measure of 2.1.2, p. 54. Source
    editions: FiniteCountingFunctionExamples.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets
  reals constructive_ereal.
From Federer Require Import CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_finite_predicate]: counting a decidable
    subset of a finite type gives its finite cardinality, Federer
    2.1.2, p. 54; supporting binary-word counting for
    the 2.3.8 counterexample. *)
Lemma counting_finite_predicate (R : realType) (I : finType) (P : pred I) :
  @counting_measure R I [set x | P x] = (#|P|%:R : R)%:E.
Proof.
have he : [set x | P x] = [set` [fset x in P]].
  apply/seteqP; split=> x hx.
  - change (x \in [fset x in P]); by rewrite inE.
  - have hx' : x \in [fset x in P] := hx; by move: hx'; rewrite inE.
by rewrite he counting_measure_finite card_imfset //= -cardE.
Qed.

(** Source for [counting_finite_whole]: the total mass of
    counting measure on a finite space is its cardinality,
    Federer 2.1.2, p. 54; supporting 2.3.8. *)
Lemma counting_finite_whole (R : realType) (I : finType) :
  @counting_measure R I setT = (#|I|%:R : R)%:E.
Proof.
have he : @setT I = [set x | predT x] by apply/seteqP; split=> x _.
by rewrite he counting_finite_predicate cardT.
Qed.
