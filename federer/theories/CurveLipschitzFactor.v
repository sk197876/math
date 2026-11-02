(** Federer (1969), 2.5.16, p. 110: since p[g(t), g(u)] <= |s(t) - s(u)|
    whenever t, u in R, there exists a unique Lipschitzian function G : im s
    -> Y with Lip(G) <= 1 and G o s = g. The function G is produced on all
    of R by choice, with the Lipschitz estimate on im s and uniqueness on im
    s. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import CurveVariationUP CurveArcLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzFactor.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).

(** Source for [arc_length_distance_abs]: the estimate
    p[g(t), g(u)] <= |s(t) - s(u)| whenever t, u in R, Federer 2.5.16,
    p. 110. *)
Lemma arc_length_distance_abs (t u : R) : mdist (g t) (g u) <= `|s t - s u|.
Proof.
case: (leP t u)=> htu.
- rewrite distrC ger0_norm ?subr_ge0 ?(arc_length_monotone hfin htu) //.
  exact (arc_length_distance hfin htu).
- rewrite ger0_norm ?subr_ge0 ?(arc_length_monotone hfin (ltW htu)) // metric_sym.
  exact (arc_length_distance hfin (ltW htu)).
Qed.

(** Source for [arc_length_factor]: the function G of Federer 2.5.16,
    p. 110, chosen on im s by G(s(t)) = g(t) and extended by the value
    g(0) off im s. *)
Definition arc_length_factor (z : R) : Y :=
  if pselect (exists t, s t = z) is left h then g (sval (cid h)) else g 0.

(** Source for [arc_length_factor_compose]: G o s = g, Federer 2.5.16,
    p. 110: two parameters with the same arc length have the same image
    by p[g(t), g(u)] <= |s(t) - s(u)|. *)
Lemma arc_length_factor_compose (t : R) : arc_length_factor (s t) = g t.
Proof.
rewrite /arc_length_factor; case: pselect=> [h|[]]; last by exists t.
apply: mdist_positivity; apply/le_anti; rewrite mdist_ge0 andbT.
by have := arc_length_distance_abs (sval (cid h)) t; rewrite (svalP (cid h)) subrr normr0.
Qed.

(** Source for [arc_length_factor_lipschitz]: Lip(G) <= 1 on im s,
    Federer 2.5.16, p. 110. *)
Lemma arc_length_factor_lipschitz (z w : R) :
  range s z -> range s w -> mdist (arc_length_factor z) (arc_length_factor w) <= `|z - w|.
Proof.
move=> [t _ <-] [u _ <-]; rewrite !arc_length_factor_compose.
exact: arc_length_distance_abs.
Qed.

(** Source for [arc_length_factor_unique]: uniqueness of G on im s,
    Federer 2.5.16, p. 110. *)
Lemma arc_length_factor_unique (G : R -> Y) :
  (forall t, G (s t) = g t) -> forall z, range s z -> G z = arc_length_factor z.
Proof. by move=> hG z [t _ <-]; rewrite hG arc_length_factor_compose. Qed.

End LipschitzFactor.
