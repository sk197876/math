(** Federer (1969), 2.5.11, p. 102: the measure beta_j over Y_j which
    vanishes on the subsets of cardinal less than aleph_j and equals one on
    the subsets of cardinal aleph_j. The cardinal bound is represented by a
    set P, as in CardinalSuccessorUP.v: a subset is small when it injects
    into P. Countable subadditivity needs that countable unions of small
    sets are small; this requirement is a separate hypothesis, proved below
    for aleph-zero and for aleph-one. Kelley, General Topology, Appendix,
    Theorem 180, p. 280 (Dover 2017 reprint of 1955), is the cardinal
    background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import CardinalSuccessorUP AlephOneArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [is_sigma_small_bound]: supporting hypothesis for the
    countable subadditivity of beta_j in Federer 2.5.11, p. 102:
    a countable union of sets of cardinal at most P has cardinal at
    most P. Kelley, Appendix, Theorem 180, p. 280. *)
Definition is_sigma_small_bound (K K' : Type) (P : set K') : Prop :=
  forall D : set (set K), countable D -> (forall B, D B -> B #<= P) ->
  \bigcup_(B in D) B #<= P.

(** Source for [cardinal_measure]: direct two-case definition of
    beta_j in Federer 2.5.11, p. 102: zero on sets of cardinal
    less than aleph_j, one on sets of cardinal aleph_j. The
    cardinal aleph_j is represented by P, so that a subset of
    smaller cardinal is one injecting into P. *)
Definition cardinal_measure (R : realType) (K K' : Type) (P : set K')
    (A : set K) : \bar R := if A #<= P then 0 else 1.

(** Source for [cardinal_measure_small]: the first clause defining
    beta_j in Federer 2.5.11, p. 102. *)
Lemma cardinal_measure_small (R : realType) (K K' : Type) (P : set K') (A : set K) :
  A #<= P -> cardinal_measure R P A = 0.
Proof. by move=> h; rewrite /cardinal_measure h. Qed.

(** Source for [cardinal_measure_large]: the second clause defining
    beta_j in Federer 2.5.11, p. 102. *)
Lemma cardinal_measure_large (R : realType) (K K' : Type) (P : set K') (A : set K) :
  ~ (A #<= P) -> cardinal_measure R P A = 1.
Proof. by move=> /negP h; rewrite /cardinal_measure (negbTE h). Qed.

(** Source for [cardinal_measure_nonnegative]: supporting
    nonnegativity of beta_j, Federer 2.5.11, p. 102. *)
Lemma cardinal_measure_nonnegative (R : realType) (K K' : Type) (P : set K') (A : set K) :
  0 <= cardinal_measure R P A.
Proof. by rewrite /cardinal_measure; case: ifP=> _ //; rewrite lee_fin ler01. Qed.

(** Source for [cardinal_measure_le1]: supporting bound one for
    the values of beta_j, Federer 2.5.11, p. 102. *)
Lemma cardinal_measure_le1 (R : realType) (K K' : Type) (P : set K') (A : set K) :
  cardinal_measure R P A <= 1.
Proof. by rewrite /cardinal_measure; case: ifP=> _ //; rewrite lee_fin ler01. Qed.

(** Source for [cardinal_measure_zero_iff]: supporting
    characterisation of the null sets of beta_j, Federer 2.5.11,
    p. 102: exactly the sets of cardinal less than aleph_j. *)
Lemma cardinal_measure_zero_iff (R : realType) (K K' : Type) (P : set K') (A : set K) :
  cardinal_measure R P A = 0 <-> A #<= P.
Proof.
rewrite /cardinal_measure; case: ifPn=> h; first by split.
by split=> // /eqP; rewrite eqe oner_eq0.
Qed.

(** Source for [cardinal_measure_one_iff]: supporting
    characterisation of the sets of beta_j measure one, Federer
    2.5.11, p. 102. *)
Lemma cardinal_measure_one_iff (R : realType) (K K' : Type) (P : set K') (A : set K) :
  cardinal_measure R P A = 1 <-> ~ (A #<= P).
Proof.
rewrite /cardinal_measure; case: ifPn=> h; last by split.
by split=> // /eqP; rewrite eqe eq_sym oner_eq0.
Qed.

(** Source for [cardinal_measure_values]: beta_j takes only the
    values zero and one, Federer 2.5.11, p. 102. *)
Lemma cardinal_measure_values (R : realType) (K K' : Type) (P : set K') (A : set K) :
  cardinal_measure R P A = 0 \/ cardinal_measure R P A = 1.
Proof. by rewrite /cardinal_measure; case: ifP=> _; [left|right]. Qed.

(** Source for [countable_sigma_small]: countable unions of countable
    sets are countable, the subadditivity requirement for beta_1 in
    Federer 2.5.11, p. 102; Kelley, Appendix, Theorem 180, p. 280. *)
Lemma countable_sigma_small (K : Type) : is_sigma_small_bound K (@setT nat).
Proof. by move=> D hD hB; exact: bigcup_countable hD hB. Qed.

(** Source for [aleph_one_sigma_small]: countable unions of sets of
    cardinal at most aleph-one have cardinal at most aleph-one, the
    subadditivity requirement for beta_2 in Federer 2.5.11, p. 102;
    Kelley, Appendix, Theorem 180, p. 280. *)
Lemma aleph_one_sigma_small (J K : choiceType) (Y : set J) :
  is_cardinal_successor (@setT nat) Y -> is_sigma_small_bound K Y.
Proof. by move=> hY D hD hB; exact: aleph_one_countable_union_bound hY hD hB. Qed.
