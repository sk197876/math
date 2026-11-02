(** Federer (1969), 2.2.10(1), p. 67: private iteration of the inseparable
    child-pair choice. Only the chosen branch pairs are stored; their
    abstract laws agree with intersections along the book's full covering
    tree. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import BorelSeparation BorelSeparationRefinement ClosedCoverTreeUP
  InseparableClosedBranchesUP InseparableClosedBranchesConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Iteration.
Context (R : realType) (T : metricType R) (Y : topologicalType) (f : T -> Y).
Context (H : set T) (hc : countable H) (hd : dense H).

(** Source for [closed_inseparable_state]: private pair of
    nonseparated closed sets in the induction for Federer
    2.2.10(1), p. 67. Nonemptiness follows from failure
    of separation and is not an additional assumption. *)
Definition closed_inseparable_state :=
  {p : set T * set T | closed p.1 /\ closed p.2 /\
    ~ borel_separated (f @` p.1) (f @` p.2)}.

(** Source for [inseparable_state_refinement]: private transition
    laws for Federer 2.2.10(1), p. 67: both closed sets
    shrink by inclusion and obey the next diameter bound. *)
Definition inseparable_state_refinement (k : nat) (s t : closed_inseparable_state) : Prop :=
  (proj1_sig t).1 `<=` (proj1_sig s).1 /\
  (proj1_sig t).2 `<=` (proj1_sig s).2 /\
  (forall x y, (proj1_sig t).1 x -> (proj1_sig t).1 y -> mdist x y <= @closed_cover_tree_scale R k) /\
  (forall x y, (proj1_sig t).2 x -> (proj1_sig t).2 y -> mdist x y <= @closed_cover_tree_scale R k).

(** Source for [inseparable_state_step_exists]: private existence
    of an inductive step in Federer 2.2.10(1), p. 67,
    by the proved small closed-cover refinement. *)
Lemma inseparable_state_step_exists k (s : closed_inseparable_state) :
  exists t, inseparable_state_refinement k s t.
Proof.
have [hC [hD hn]] := proj2_sig s.
have [P [Q [hP [hQ [hPC [hQD [hp [hq hns]]]]]]]] :=
  @closed_image_small_inseparable_refinement R T Y f H (proj1_sig s).1 (proj1_sig s).2
    (@closed_cover_tree_scale R k) hc hd hC hD (closed_cover_tree_scale_positive R k) hn.
exists (exist _ (P,Q) (conj hP (conj hQ hns))); by split=> //; split=> //; split.
Qed.

(** Source for [inseparable_state_step]: private selection of
    a proved transition witness in Federer 2.2.10(1), p. 67. *)
Definition inseparable_state_step k s := projT1 (cid (inseparable_state_step_exists k s)).

(** Source for [inseparable_state_step_laws]: the private choice
    satisfies its refinement laws for Federer 2.2.10(1), p. 67. *)
Lemma inseparable_state_step_laws k s :
  inseparable_state_refinement k s (inseparable_state_step k s).
Proof. exact: projT2 (cid (inseparable_state_step_exists k s)). Qed.

(** Source for [inseparable_state_branch]: private inductive
    sequence of chosen pairs in Federer 2.2.10(1), p. 67.
    This recursion is hidden behind the branch-law interface. *)
Fixpoint inseparable_state_branch (s : closed_inseparable_state) (n : nat) : closed_inseparable_state :=
  if n is k.+1 then inseparable_state_step k (inseparable_state_branch s k) else s.

(** Source for [inseparable_state_branch_nested]: supporting
    nesting of all descendants in Federer 2.2.10(1), p. 67,
    by induction on the number of successive refinements. *)
Lemma inseparable_state_branch_nested s n k :
  (proj1_sig (inseparable_state_branch s (n+k))).1 `<=` (proj1_sig (inseparable_state_branch s n)).1 /\
  (proj1_sig (inseparable_state_branch s (n+k))).2 `<=` (proj1_sig (inseparable_state_branch s n)).2.
Proof.
elim: k=> [|k IH]; first by rewrite addn0; split.
rewrite addnS /=; have h := inseparable_state_step_laws (n+k)%N (inseparable_state_branch s (n+k)).
split; [exact: subset_trans h.1 IH.1|exact: subset_trans h.2.1 IH.2].
Qed.

(** Source for [inseparable_closed_branches_exists]: supporting branch
    existence in Federer 2.2.10(1), p. 67, under the assumed failure of
    separation. Closedness and shrinking follow from the transitions;
    failure of separation ensures that both branches stay nonempty. No
    completeness or continuity is needed until the later contradiction. *)
Theorem inseparable_closed_branches_exists (C D : set T) :
  closed C -> closed D -> ~ borel_separated (f @` C) (f @` D) ->
  exists P Q, is_inseparable_closed_branches f C D P Q.
Proof.
move=> hC hD hn.
pose s : closed_inseparable_state := exist _ (C,D) (conj hC (conj hD hn)).
pose P n := (proj1_sig (inseparable_state_branch s n)).1.
pose Q n := (proj1_sig (inseparable_state_branch s n)).2.
have hl n := proj2_sig (inseparable_state_branch s n).
exists P,Q; constructor.
- by [].
- by [].
- move=> n; exact: (hl n).1.
- move=> n; exact: (hl n).2.1.
- move=> n; have [hne _] := non_borel_separated_nonempty (hl n).2.2.
  have [y [x hx _]] := hne; by exists x.
- move=> n; have [_ hne] := non_borel_separated_nonempty (hl n).2.2.
  have [y [x hx _]] := hne; by exists x.
- move=> n m hnm; have hm : m = (n+(m-n))%N by rewrite subnKC.
  rewrite hm; exact: (inseparable_state_branch_nested s n (m-n)).1.
- move=> n m hnm; have hm : m = (n+(m-n))%N by rewrite subnKC.
  rewrite hm; exact: (inseparable_state_branch_nested s n (m-n)).2.
- move=> n; exact: (inseparable_state_step_laws n (inseparable_state_branch s n)).2.2.1.
- move=> n; exact: (inseparable_state_step_laws n (inseparable_state_branch s n)).2.2.2.
- move=> n; exact: (hl n).2.2.
Qed.
End Iteration.
