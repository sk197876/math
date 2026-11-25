(** Federer (1969), 3.1.4, p. 215: choose one pair of
    radius-index sequences for all finitely many coordinate families.
    The sum of all losses is made smaller than an arbitrary tolerance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureCountableClosure FiniteFamilyConullExhaustion MeasureTwoStageCutoffSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_family_two_stage_cutoffs]: the simultaneous
    p_j,q_j and large set H in Federer 3.1.4, p. 215. The finite
    coordinate intersections are grouped before distributing the
    geometric loss budget, so the requested total error is arbitrary. *)
Theorem finite_family_two_stage_cutoffs (R : realType) (X : choiceType) (J : finType)
    (mu : set X -> \bar R) (A : J -> set X) (E : set X)
    (B : J -> nat -> nat -> set X) (C : J -> nat -> nat -> nat -> set X) :
  is_measure mu -> E `<=` \bigcap_i A i -> mu E < +oo ->
  (forall i j p, measure_measurable mu (B i j p)) ->
  (forall i j p q, (p<=q)%N -> B i j p `<=` B i j q) ->
  (forall i j, (\bigcup_p B i j p)=A i) ->
  (forall i j p q, measure_measurable mu (C i j p q)) ->
  (forall i j p q r, (q<=r)%N -> C i j p q `<=` C i j p r) ->
  (forall i j p, mu (B i j p `\` \bigcup_q C i j p q)=0) ->
  forall e : R, (0<e)%R -> exists p q : nat -> nat,
    mu (E `\` \bigcap_j \bigcap_i C i j (p j) (q j))<e%:E.
Proof.
move=> hm hEA hE hB hBm hBe hC hCm hCn e he.
pose Bf j p := \bigcap_i B i j p.
pose Cf j p q := \bigcap_i C i j p q.
have hBf j p : measure_measurable mu (Bf j p).
  apply: (@measure_measurable_countable_intersection R X [the choiceType of (J : Type)]
    mu hm setT (fun i=>B i j p) (countableP _))=> i _; exact: hB.
have hBfm j p q : (p<=q)%N -> Bf j p `<=` Bf j q.
  move=> hpq x hx i _; exact: hBm i j p q hpq x (hx i Logic.I).
have hBfn j : mu (E `\` \bigcup_p Bf j p)=0.
  apply: (@finite_conull_increasing_exhaustion R X J mu E (fun i p=>B i j p) hm).
  - by move=> i p q; exact: hBm.
  - move=> i; rewrite hBe.
    have hempty : E `\` A i=set0.
      apply/seteqP; split=> x; last by [].
      move=> [hx hn]; apply: hn; exact: hEA x hx i Logic.I.
    by rewrite hempty (measure_empty hm).
have hCf j p q : measure_measurable mu (Cf j p q).
  apply: (@measure_measurable_countable_intersection R X [the choiceType of (J : Type)]
    mu hm setT (fun i=>C i j p q) (countableP _))=> i _; exact: hC.
have hCfm j p q r : (q<=r)%N -> Cf j p q `<=` Cf j p r.
  move=> hqr x hx i _; exact: hCm i j p q r hqr x (hx i Logic.I).
have hCfn j p : mu (Bf j p `\` \bigcup_q Cf j p q)=0.
  apply: (@finite_conull_increasing_exhaustion R X J mu (Bf j p)
    (fun i q=>C i j p q) hm).
  - by move=> i q r; exact: hCm.
  - move=> i; apply: (@measure_null_subset R X mu hm _ _ _ (hCn i j p)).
    move=> x [hx hn]; split=> //; exact: hx i Logic.I.
exact: (measure_two_stage_diagonal_cutoffs hm hE hBf hBfm hBfn hCf hCfm hCfn he).
Qed.
