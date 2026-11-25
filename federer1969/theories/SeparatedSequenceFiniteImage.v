(** Supporting metric argument for the finite-image-density correction to
    Federer (1969), 2.4.12, p. 87, line 18, in his May-1987 erratum p. 2.
    The lemmas below isolate the separation argument, valid in an arbitrary
    metric space. They do not by themselves assert a measure-theoretic
    counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_sequence_close_map_injective]: Supporting Federer
    2.4.12, p. 87.A uniform approximation closer than half the separation
    cannot identify two sequence values. *)
Lemma separated_sequence_close_map_injective (R : realType) (Y : metricType R)
    (e g : nat -> Y) (d : R) :
  (forall n m, n <> m -> d <= mdist (e n) (e m)) ->
  (forall n, mdist (e n) (g n) < d/2) -> injective g.
Proof.
move=> hs hg n m he; have [hnm|hnm] := pselect (n=m); first exact hnm.
exfalso.
have ht := metric_triangle (e n) (g n) (e m).
rewrite he [mdist (g m) (e m)]metric_sym in ht.
have hsum := ltrD (hg n) (hg m); rewrite -splitr he in hsum.
have hbad := le_lt_trans (hs n m hnm) (le_lt_trans ht hsum).
by move: hbad; rewrite ltxx.
Qed.

(** Source for [separated_sequence_no_finite_image_approximation]: This
    abstracts the metric part of the counterexample motivating Federer's
    erratum p. 2, book p. 87 line 18. *)
Theorem separated_sequence_no_finite_image_approximation
    (R : realType) (Y : metricType R) (e g : nat -> Y) (d : R) :
  (forall n m, n <> m -> d <= mdist (e n) (e m)) ->
  finite_set (g @` setT) -> ~ (forall n, mdist (e n) (g n) < d/2).
Proof.
move=> hs hfinite hg.
have hinj := separated_sequence_close_map_injective hs hg.
have hpre : {in g @^-1` (g @` setT) &, injective g}.
  by move=> n m _ _; exact: hinj.
have hf := finite_preimage hpre hfinite.
have he : g @^-1` (g @` setT)=setT.
  apply/seteqP; split=> // n _; exists n=> //.
rewrite he in hf; exact: infinite_nat hf.
Qed.
