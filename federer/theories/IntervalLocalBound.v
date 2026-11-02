(** Federer (1969), 2.2.7, p. 64, proof of the convex-domain criterion. This
    supporting lemma isolates the argument on the segment parameter [0,1].
    We use the local distance bound itself to show that the supremum belongs
    to S; this supplies quantitatively the closedness step that Federer
    expresses using continuity. No mean value or differentiation theorem is
    imported. Source context: LipschitzUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_local_metric_bound]: supporting segment
    argument for Federer 2.2.7, p. 64. If every parameter r has
    a neighborhood on which distances from g(r) are bounded by
    C times the parameter distance, then the endpoint distance is
    at most C. The proof uses precisely the printed set S, its
    supremum, and extension to the right if that supremum is below 1. *)
Lemma interval_local_metric_bound (R : realType) (U : metricType R)
    (g : R -> U) (C : R) :
  0 <= C ->
  (forall r, 0 <= r -> r <= 1 -> exists d, 0 < d /\
    forall t, 0 <= t -> t <= 1 -> `|t-r| < d ->
      mdist (g r) (g t) <= C * `|t-r|) ->
  mdist (g 0) (g 1) <= C.
Proof.
move=> hC hlocal.
pose S := [set t | 0 <= t /\ t <= 1 /\ mdist (g 0) (g t) <= C*t].
have h0 : S 0 by split; [exact: lexx|split; rewrite ?mdistxx ?mulr0 ?ler01].
have hn : S !=set0 by exists 0.
have hu : ubound S 1 by move=> t [_ [ht _]].
have hb : has_ubound S by exists 1.
have hs : has_sup S by split.
pose r := sup S.
have hr0 : 0 <= r := ub_le_sup hb h0.
have hr1 : r <= 1 := ge_sup hn hu.
have [d [hd hstep]] := hlocal r hr0 hr1.
have [t [ht0 [ht1 htS]] htnear] := sup_adherent hd hs.
have htr : t <= r := ub_le_sup hb (conj ht0 (conj ht1 htS)).
have hgap : r-t < d by rewrite ltrBlDr addrC -ltrBlDr.
have hnorm : `|t-r| = r-t.
  by rewrite -opprB normrN ger0_norm // subr_ge0.
have hrS : S r.
  split=> //; split=> //.
  have he := hstep t ht0 ht1; rewrite hnorm in he.
  have he' : mdist (g t) (g r) <= C*(r-t).
    rewrite metric_sym; exact: he hgap.
  apply: le_trans (metric_triangle (g 0) (g t) (g r)) _.
  have hbnd := lerD htS he'.
  by rewrite -mulrDr addrCA subrr addr0 in hbnd.
have hr : r = 1.
  apply/eqP; rewrite eq_le hr1 /= leNgt; apply/negP=> hrlt.
  have hru : r < Order.min 1 (r+d) by rewrite lt_min hrlt ltrDl hd.
  have [hrr' hr'u] := midf_lt hru.
  pose r' := (r + Order.min 1 (r+d)) / 2.
  have hr'0 : 0 <= r' := le_trans hr0 (ltW hrr').
  have hr'1 : r' <= 1.
    apply: le_trans (ltW hr'u) _; by rewrite ge_min lexx.
  have hr'd : r'-r < d.
    rewrite ltrBlDr addrC; apply: lt_le_trans hr'u _; by rewrite ge_min lexx orbT.
  have hnorm' : `|r'-r| = r'-r by rewrite ger0_norm // subr_ge0; exact: ltW hrr'.
  have he := hstep r' hr'0 hr'1; rewrite hnorm' in he.
  have hr'S : S r'.
    split=> //; split=> //.
    apply: le_trans (metric_triangle (g 0) (g r) (g r')) _.
    have hbnd := lerD hrS.2.2 (he hr'd).
    by rewrite -mulrDr addrCA subrr addr0 in hbnd.
  have := ub_le_sup hb hr'S.
  by rewrite leNgt hrr'.
by move: hrS.2.2; rewrite hr mulr1.
Qed.
