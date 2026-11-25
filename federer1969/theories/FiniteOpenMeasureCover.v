(** Federer (1969), proof of 2.8.2, p. 142, first sentence: the ambient
    metric space is covered by countably many bounded sets. The cover is
    specified by its laws before its existence is proved. No separability or
    nonempty-space premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CoveringFamilyUP CoveringFamilyLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_open_measure_cover]: Supporting Federer 2.8.2, p.
    142.It is weaker than finiteness on all bounded sets. *)
Record is_finite_open_measure_cover (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (U : nat -> set X) : Prop := {
  (** Source for [finite_open_cover_open]: supporting Federer 2.8.2, p. 142. *)
  finite_open_cover_open : forall n, open (U n);
  (** Source for [finite_open_cover_finite]: supporting Federer 2.8.2, p. 142. *)
  finite_open_cover_finite : forall n, mu (U n) < +oo;
  (** Source for [finite_open_cover_covers]: the sequence covers X, as used in
    Federer 2.8.2, p. 142. *)
  finite_open_cover_covers : setT `<=` \bigcup_n U n
}.

(** Source for [covering_context_finite_open_cover]: the countable bounded
    covering used in Federer 2.8.2, p. 142, with open balls so that. A
    center is chosen only when X is nonempty; for an empty ambient space the
    constant empty cover works. *)
Theorem covering_context_finite_open_cover (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) :
  is_covering_theory_context F mu ->
  exists U, is_finite_open_measure_cover mu U.
Proof.
move=> hc; case: (pselect (exists x : X, True))=> [[a _]|hempty].
- pose U n := metric_open_ball a (n.+1)%:R.
  exists U; constructor.
  + move=> n; exact: covering_open_ball_open.
  + move=> n; exact (@covering_context_ball_finite R X F mu hc a (n.+1)%:R (ler0n _ _)).
  + move=> x _.
    pose k := Num.bound (mdist a x).
    have hk : (mdist a x < k%:R)%R.
      apply: archi_boundP; exact: mdist_ge0.
    have hs : (k%:R < k.+1%:R :> R)%R by rewrite ltr_nat ltnSn.
    exists k; first exact Logic.I.
    exact: lt_trans hk hs.
- exists (fun _ : nat => (@set0 X)); constructor.
  + by move=> n; exact: open0.
  + move=> n; rewrite (measure_empty (covering_context_measure hc)); exact: ltry.
  + move=> x _; exfalso; apply: hempty; by exists x.
Qed.
