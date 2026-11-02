(** Consequences of the successive-selection laws in Federer (1969), 2.8.12,
    p. 149. The decreasing remainders and mutually disjoint parameter
    selections are used in the finite cardinal contradiction. This module
    uses only the abstract iteration laws. Source context and indexing:
    RadiusSelectionIterationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusSelectionIterationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Laws.
Variable R : realType.
Variable X : metricType R.
Variable tau : R.
Variable Q : set (X*R).
Variables W S : nat -> set (X*R).
Hypothesis h : is_radius_selection_iteration tau Q W S.

(** Source for [radius_iteration_decreasing_step]: successive
    eligible sets decrease in Federer 2.8.12, p. 149.
    Supporting consequence of removing a selected subset. *)
Lemma radius_iteration_decreasing_step n : W n.+1 `<=` W n.
Proof. by rewrite (radius_iteration_remainder h); move=> p []. Qed.

(** Source for [radius_iteration_decreasing]: later remainders
    are contained in every earlier one, supporting the selection
    of all witnesses near a hypothetical remaining pair in
    Federer 2.8.12, p. 149. *)
Lemma radius_iteration_decreasing i j : (i <= j)%N -> W j `<=` W i.
Proof.
move=> hij; elim: j hij=> [|j ih].
- by rewrite leqn0=> /eqP ->.
- rewrite leq_eqVlt; move=> /orP [/eqP ->|hij]; first exact: subset_refl.
  move=> p hp; exact: ih hij p (radius_iteration_decreasing_step hp).
Qed.

(** Source for [radius_iteration_remainder_subset]: each
    remainder is a subset of the original Q, Federer 2.8.12,
    p. 149. Supporting law for restricted radius bounds. *)
Lemma radius_iteration_remainder_subset n : W n `<=` Q.
Proof.
rewrite -(radius_iteration_initial h); exact: radius_iteration_decreasing (leq0n n).
Qed.

(** Source for [radius_iteration_selected_subset]: every selected
    stage is a subset of Q, Federer 2.8.12, p. 149,
    by its membership in the current remainder. *)
Lemma radius_iteration_selected_subset n : S n `<=` Q.
Proof.
move=> p hp; apply: radius_iteration_remainder_subset.
exact (@radius_selection_members R X tau (W n) (S n) (radius_iteration_selection h n) p hp).
Qed.

(** Source for [radius_iteration_later_avoids_selection]: a later
    remainder avoids each earlier selection, Federer 2.8.12,
    p. 149. This proves the distinguished remaining pair differs
    from every selected witness. *)
Lemma radius_iteration_later_avoids_selection i j : (i < j)%N ->
  forall p, W j p -> ~ S i p.
Proof.
move=> hij p hp.
have hi := @radius_iteration_decreasing i.+1 j hij p hp.
by move: hi; rewrite (radius_iteration_remainder h)=> -[_ hn].
Qed.

(** Source for [radius_iteration_distinct_stages]: the sets
    R_j of parameters are disjoint for distinct stages in
    Federer 2.8.12, p. 149. Distinct selected witnesses
    therefore represent distinct parameters. *)
Lemma radius_iteration_distinct_stages i j : i <> j ->
  forall p, S i p -> ~ S j p.
Proof.
move=> hne p hp hq.
case: (ltngtP i j)=> [hij|hji|heq]; last by apply: hne.
- apply: (@radius_iteration_later_avoids_selection i j hij p _ hp).
  exact (@radius_selection_members R X tau (W j) (S j) (radius_iteration_selection h j) p hq).
- apply: (@radius_iteration_later_avoids_selection j i hji p _ hq).
  exact (@radius_selection_members R X tau (W i) (S i) (radius_iteration_selection h i) p hp).
Qed.

(** Source for [radius_iteration_selected_before]: the identity
    of the finite remaining set as the complement of all earlier
    selections in Federer 2.8.12, p. 149, expressed pointwise.
    It yields the coloring once the final remainder is empty. *)
Lemma radius_iteration_selected_before n p : Q p -> ~ W n p ->
  exists i : nat, (i < n)%N /\ S i p.
Proof.
elim: n=> [|n ih] hQ hn.
- exfalso; apply: hn; by rewrite (radius_iteration_initial h).
- case: (pselect (W n p))=> [hp|hp].
  + exists n; split; first exact: ltnSn.
    apply: contrapT=> hs; apply: hn.
    rewrite (radius_iteration_remainder h); by split.
  + have [i [hi hs]] := ih hQ hp; exists i; split=> //.
    exact: ltn_trans hi (ltnSn n).
Qed.
End Laws.
