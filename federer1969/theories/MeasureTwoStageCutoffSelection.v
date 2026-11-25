(** Federer (1969), 3.1.4, p. 215: choose p_j and q_j
    with summable losses, then intersect the resulting good sets.
    This supporting measure argument leaves the finite test set E arbitrary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit
  MeasureGeometricCover GeometricErrorBudget FiniteMeasureExhaustionCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_two_stage_small_complement]: the two
    finite-measure approximations on Federer 3.1.4, p. 215.
    Half of the requested tolerance is allocated to each stage. *)
Lemma measure_two_stage_small_complement (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : set X) (B : nat -> set X)
    (C : nat -> nat -> set X) :
  is_measure mu -> mu E < +oo ->
  (forall p, measure_measurable mu (B p)) ->
  (forall p q, (p<=q)%N -> B p `<=` B q) ->
  mu (E `\` \bigcup_p B p)=0 ->
  (forall p q, measure_measurable mu (C p q)) ->
  (forall p q r, (q<=r)%N -> C p q `<=` C p r) ->
  (forall p, mu (B p `\` \bigcup_q C p q)=0) ->
  forall e : R, (0<e)%R -> exists p q, mu (E `\` C p q)<e%:E.
Proof.
move=> hm hE hB hBm hBn hC hCm hCn e he.
have he2 : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have [p hp] := finite_measure_exhaustion_cutoff hm hE hB hBm hBn he2.
have hEB : mu (E `&` B p) < +oo.
  apply: le_lt_trans _ hE; apply: (measure_mono hm)=> x [hx _]; exact hx.
have hnull : mu ((E `&` B p) `\` \bigcup_q C p q)=0.
  apply: (@measure_null_subset R X mu hm _ _ _ (hCn p))=> x [[_ hx] hn]; by split.
have [q hq] := finite_measure_exhaustion_cutoff hm hEB (hC p) (hCm p) hnull he2.
exists p,q.
have hcover : E `\` C p q `<=` (E `\` B p) `|` ((E `&` B p) `\` C p q).
  move=> x [hx hn]; case: (pselect (B p x))=> hb.
  - right; by split=> //; split.
  - left; by split.
have hh := measure_binary_cover hm hcover.
have hb := lteD (hp p (leqnn p)) (hq q (leqnn q)).
have hid : (e/2)%R%:E+(e/2)%R%:E=e%:E.
  rewrite -EFinD; congr (_%:E); lra.
rewrite hid in hb; exact: le_lt_trans hh hb.
Qed.

(** Source for [measure_two_stage_diagonal_cutoffs]: the sequences
    p_j,q_j and their common good set H in Federer 3.1.4,
    p. 215. The geometric budget absorbs the finite-coordinate
    losses once they have been grouped at each j. *)
Theorem measure_two_stage_diagonal_cutoffs (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : set X) (B : nat -> nat -> set X)
    (C : nat -> nat -> nat -> set X) :
  is_measure mu -> mu E < +oo ->
  (forall j p, measure_measurable mu (B j p)) ->
  (forall j p q, (p<=q)%N -> B j p `<=` B j q) ->
  (forall j, mu (E `\` \bigcup_p B j p)=0) ->
  (forall j p q, measure_measurable mu (C j p q)) ->
  (forall j p q r, (q<=r)%N -> C j p q `<=` C j p r) ->
  (forall j p, mu (B j p `\` \bigcup_q C j p q)=0) ->
  forall e : R, (0<e)%R -> exists p q : nat -> nat,
    mu (E `\` \bigcap_j C j (p j) (q j))<e%:E.
Proof.
move=> hm hE hB hBm hBn hC hCm hCn e he.
have hchoose : forall j, exists pq : nat*nat,
    mu (E `\` C j pq.1 pq.2)<(geometric_error_budget e j)%:E.
  move=> j; have [p [q hpq]] := measure_two_stage_small_complement hm hE
    (hB j) (hBm j) (hBn j) (hC j) (hCm j) (hCn j) (geometric_error_budget_positive j he).
  by exists (p,q).
have [pq hpq] := choice hchoose.
exists (fun j=>(pq j).1),(fun j=>(pq j).2).
apply: (measure_geometric_cover_bound hm he _ hpq).2.
move=> x [hx hn].
have hex : exists j, ~C j (pq j).1 (pq j).2 x.
  apply: contrapT=> hnone; apply: hn=> j _; apply: contrapT=> hj; apply: hnone; by exists j.
have [j hj] := hex; exists j=> //; by split.
Qed.
