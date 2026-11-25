(** Consequences of the fixed-open-cover infimum supporting Federer (1969),
    2.10.1, p. 170. These proofs use only the abstract specification; no
    witness is selected or unfolded. Source context, corrected reference and
    the whole-space cover convention: OpenRefiningEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum OpenRefiningEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_refining_envelope_nonnegative]: supporting
    nonnegativity of the fixed-cover infimum in the alternative
    formula of Federer 2.10.1, p. 170. *)
Lemma open_refining_envelope_nonnegative (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) (nu : set X -> \bar R) :
  is_open_refining_envelope S cost H nu -> forall A, 0<=nu A.
Proof.
move=> hn A; apply: (open_refining_envelope_greatest hn)=> G _ _ _.
exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [open_refining_envelope_unique]: supporting
    uniqueness from the infimum laws of Federer 2.10.1,
    p. 170, applied to a fixed refinement family. *)
Lemma open_refining_envelope_unique (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X))
    (nu xi : set X -> \bar R) :
  is_open_refining_envelope S cost H nu -> is_open_refining_envelope S cost H xi ->
  forall A, nu A=xi A.
Proof.
move=> hn hx A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (open_refining_envelope_greatest hx)=> G hc hr hcov.
  exact (@open_refining_envelope_lower R X J S cost H nu hn A G hc hr hcov).
- apply: (open_refining_envelope_greatest hn)=> G hc hr hcov.
  exact (@open_refining_envelope_lower R X J S cost H xi hx A G hc hr hcov).
Qed.

(** Source for [open_refining_envelope_approximation]: supporting
    strict-upper-bound choice for the open-refining covers in
    Federer 2.10.1, p. 170, corrected reference
    Federer1955 Theorem 2.5, pp. 291–292. *)
Lemma open_refining_envelope_approximation (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X))
    (nu : set X -> \bar R) (A : set X) (b : \bar R) :
  is_open_refining_envelope S cost H nu -> nu A<b ->
  exists G : set J, countable G /\ (forall j, G j -> generator_refines_cover S H j) /\
    A `<=` \bigcup_(j in G) S j /\ nonnegative_sum G cost<b.
Proof.
move=> hn hb; apply: contrapT=> hnone.
have hle : b<=nu A.
  apply: (open_refining_envelope_greatest hn)=> G hc hr hcov.
  rewrite leNgt; apply/negP=> hlt; apply: hnone.
  exists G; by split=> //; split=> //; split.
by have := lt_le_trans hb hle; rewrite ltxx.
Qed.
