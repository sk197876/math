(** Federer (1969), 2.10.20, pp. 181–182: even and odd shell subseries are
    each bounded by the supremum of bounded-ball masses. Neither item states
    this radial exhaustion theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MetricClosedBalls RadialShells NonnegativeSum
  NonnegativeSumNatPrefix NonnegativeSeriesParity SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_uniform_separated_union_bound]: supporting
    separation law used for the shell sums in
    2.10.20, p. 182. The positive gap t is fixed;
    a scale approximation satisfies this law when its
    diameter cutoff is strictly smaller than t. *)
Definition has_uniform_separated_union_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (t : R) :=
  forall A B : set X, (forall x, A x -> forall y, B y -> (t<=mdist x y)%R) ->
    mu A+mu B<=mu (A `|` B).

(** Source for [radial_shell_parity_prefix_bound]: supporting
    finite same-parity sum estimate in 2.10.20,
    p. 182. Separation replaces measurability of the
    individual shells; no general continuity below is used. *)
Lemma radial_shell_parity_prefix_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) (t : R) (p : nat) :
  is_measure mu -> (0<t)%R -> has_uniform_separated_union_bound mu t -> forall N,
  nonnegative_sum [set k | (k<N)%N]
    (fun k => mu (A `&` metric_radial_shell a t (k.*2+p)%N))<=
  mu (set_sequence_prefix (fun k => A `&` metric_radial_shell a t (k.*2+p)%N) N).
Proof.
move=> hm ht hsep; elim=> [|N IH].
- by rewrite nonnegative_sum_nat_prefix_zero set_sequence_prefix_zero (measure_empty hm).
- rewrite nonnegative_sum_nat_prefix_succ; last by move=> k; exact: (@measure_nonnegative R X mu hm _).
  rewrite set_sequence_prefix_succ.
  apply: le_trans (leeD IH (lexx _)) _; apply: hsep.
  move=> x [k hk [_ hxs]] y [_ hys].
  exact: (@metric_radial_shell_parity_separated R X a t p k N ht hk x hxs y hys).
Qed.

(** Source for [radial_shell_series_bound]: supporting
    bound by twice the bounded-ball supremum in
    2.10.20, p. 182. Existing abstract nonnegative
    sums combine the two parity estimates; shell
    endpoints may overlap between different parities. *)
Theorem radial_shell_series_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (a : X) (A : set X) (t : R) (s : \bar R) :
  is_measure mu -> (0<t)%R -> has_uniform_separated_union_bound mu t ->
  (forall r : R, mu (A `&` metric_closed_ball a r)<=s) ->
  nonnegative_sum setT (fun n => mu (A `&` metric_radial_shell a t n))<=s+s.
Proof.
move=> hm ht hsep hbound.
apply: nonnegative_series_parity_bound; first by move=> n; exact: (@measure_nonnegative R X mu hm _).
move=> p; apply: nonnegative_series_prefix_bound=> N.
apply: le_trans (@radial_shell_parity_prefix_bound R X mu a A t p hm ht hsep N) _.
apply: le_trans _ (hbound (((N.*2+p).+1)%:R*t)%R).
apply: (@measure_mono R X mu hm)=> x [k hk [hx /andP[_ hdist]]].
split=> //; apply: le_trans hdist _.
have hidx : ((k.*2+p).+1<=(N.*2+p).+1)%N.
  change ((k.*2+p<=N.*2+p)%N).
  rewrite leq_add2r leq_double; exact: ltnW hk.
have hcast : ((((k.*2+p).+1)%:R : R)<=(N.*2+p).+1%:R)%R by rewrite ler_nat.
have hh := ler_wpM2r (ltW ht) hcast.
exact hh.
Qed.
