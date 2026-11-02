(** Federer (1969), 2.2.5, pp. 62–63, and 2.2.7, p. 64: a map continuous at
    every point of a compact metric set is uniformly continuous there. This
    supports the assertion "D^{k+1} f is uniformly continuous on C" in
    3.1.15, p. 228. The proof is the Lebesgue-number argument: the finite
    subcover of 2.2.5 by half-radius balls yields a positive minimum radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  finmap.
From Federer Require Import MetricClosedBalls CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [seq_positive_lower_bound]: supporting finite minimum of
    positive radii in the finite-subcover step of Federer 2.2.5, p. 63. *)
Lemma seq_positive_lower_bound (R : realType) (T : eqType) (s : seq T) (g : T -> R) :
  (forall a, a \in s -> 0 < g a) ->
  exists delta : R, 0 < delta /\ forall a, a \in s -> delta <= g a.
Proof.
elim: s=> [|a s ih] hpos.
- by exists 1; split=> // b; rewrite in_nil.
- have [delta [hd hle]] := ih (fun b hb => hpos b (@mem_behead T (a :: s) b hb)).
  exists (Order.min delta (g a)); split; first by rewrite lt_min hd (hpos a (mem_head a s)).
  move=> b; rewrite in_cons=> /orP [/eqP ->|hb]; first by rewrite ge_min lexx orbT.
  by rewrite ge_min (hle b hb).
Qed.

(** Source for [compact_uniform_continuity]: Federer 2.2.5, pp. 62–63, and
    2.2.7, p. 64, supporting uniform continuity on compact sets, used for
    "D^{k+1} f is uniformly continuous on C" in 3.1.15, p. 228. Each point a
    of K has a radius d(a) for e/2; the balls of radius d(a)/2 cover K; a
    finite subcover gives a positive minimum delta; two points of K at
    distance below delta lie within d(a0) of a common centre a0. *)
Theorem compact_uniform_continuity (R : realType) (T U : metricType R) (K : set T) (phi : T->U) :
  compact K ->
  (forall a, K a -> forall e : R, 0<e -> exists d : R, 0<d /\
    forall b, K b -> mdist a b<d -> mdist (phi a) (phi b)<e) ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall a b, K a -> K b -> mdist a b<d -> mdist (phi a) (phi b)<e.
Proof.
move=> hK hc e he.
have he2 : 0 < e/2 by rewrite divr_gt0.
have hex : forall a : T, exists d : R, 0 < d /\
    (K a -> forall b, K b -> mdist a b < d -> mdist (phi a) (phi b) < e/2).
  move=> a; case: (pselect (K a))=> [ha|hna].
  - by have [d [hd hb]] := hc a ha (e/2) he2; exists d; split.
  - by exists 1; split=> // ha; exfalso; exact: hna ha.
have [d hd] := choice hex.
pose F (a : T) : set T := [set b | mdist a b < d a / 2].
have hopen : forall a, K a -> open (F a) by move=> a _; exact: metric_open_ball_open.
have hcov : K `<=` \bigcup_(a in K) F a.
  by move=> a ha; exists a=> //; rewrite /F /= mdistxx divr_gt0 //; exact: (proj1 (hd a)).
have [D' hD' hKD'] := compact_open_finite_cover hK hopen hcov.
have hpos : forall a, a \in enum_fset D' -> 0 < d a / 2.
  by move=> a _; rewrite divr_gt0 //; exact: (proj1 (hd a)).
have [delta [hdelta hle]] := seq_positive_lower_bound hpos.
exists delta; split=> // a b ha hb hab.
have [a0 ha0 haa0] := hKD' a ha.
have hKa0 : K a0 := set_mem (hD' a0 ha0).
have hle0 : delta <= d a0 / 2 := hle a0 ha0.
have ha0a : mdist a0 a < d a0.
  rewrite [d a0]splitr; apply: (lt_le_trans haa0); rewrite lerDl.
  by apply: ltW; rewrite divr_gt0 //; exact: (proj1 (hd a0)).
have ha0b : mdist a0 b < d a0.
  apply: (le_lt_trans (metric_triangle a0 a b)).
  rewrite [d a0]splitr; exact: (ltrD haa0 (lt_le_trans hab hle0)).
have hpa : mdist (phi a0) (phi a) < e/2 := (proj2 (hd a0)) hKa0 a ha ha0a.
have hpb : mdist (phi a0) (phi b) < e/2 := (proj2 (hd a0)) hKa0 b hb ha0b.
apply: (le_lt_trans (metric_triangle (phi a) (phi a0) (phi b))).
rewrite [e]splitr (metric_sym (phi a) (phi a0)); exact: (ltrD hpa hpb).
Qed.
