(** Federer (1969), 3.1.1, p. 210: geometric increment bounds
    make the inverse-function iterates Cauchy, and completeness supplies
    their limit. The scalar decay uses the project's Archimedean proof. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra ring.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RecurrentContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_increment_tail_bound]: telescoping triangle
    inequality supporting the geometric convergence argument in Federer
    3.1.1, p. 210. Any nonnegative tail budget whose consecutive losses
    bound increments bounds every later displacement. *)
Lemma norm_increment_tail_bound (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (u : nat -> X) (t : nat -> R) :
  (forall n, 0 <= t n) ->
  (forall n, N (u n.+1-u n) <= t n-t n.+1) ->
  forall n m, (n <= m)%N -> N (u m-u n) <= t n.
Proof.
move=> ht hs n m hnm.
have htail k : N (u (n+k)%N-u n)+t (n+k)%N <= t n.
  elim: k=> [|k ih].
  - by rewrite addn0 subrr (real_seminorm_zero hN.1) add0r.
  - rewrite addnS.
    have heq : u (n+k)%N.+1-u n =
        (u (n+k)%N.+1-u (n+k)%N)+(u (n+k)%N-u n) by rewrite addrA subrK.
    have htri : N (u (n+k)%N.+1-u n) <=
        N (u (n+k)%N.+1-u (n+k)%N)+N (u (n+k)%N-u n).
      rewrite {1}heq; exact: real_seminorm_triangle hN.1 _ _.
    have hb := hs (n+k)%N; by lra.
have hh := htail (m-n)%N; rewrite subnKC // in hh.
have hm := ht m; by lra.
Qed.

(** Source for [norm_geometric_increments_cauchy]: the implication
    from the displayed geometric increment estimate to a Cauchy sequence
    in Federer 3.1.1, p. 210. The explicit tail is c^n a/(1-c); no external
    summation or contraction-mapping theorem is used. *)
Lemma norm_geometric_increments_cauchy (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) (u : nat -> X) (c a : R) :
  0 < c < 1 -> 0 <= a ->
  (forall n, N (u n.+1-u n) <= c^+n*a) ->
  cauchy ((fun n => (u n : real_norm_metric_space hN)) @ \oo).
Proof.
move=> hc ha hs; have hc0 := (andP hc).1; have hc1 := (andP hc).2.
have hd : 0 < 1-c by rewrite subr_gt0.
have hd0 : 1-c != 0 := lt0r_neq0 hd.
pose t := fun n => c^+n*a/(1-c).
have ht : forall n, 0 <= t n.
  move=> n; apply: divr_ge0; last exact: ltW hd.
  apply: mulr_ge0=> //; exact: exprn_ge0 (ltW hc0).
have hstep : forall n, t n-t n.+1 = c^+n*a.
  move=> n; rewrite /t exprS.
  have heq : c^+n*a-c*c^+n*a = (c^+n*a)*(1-c) by ring.
  by rewrite -mulrBl heq mulfK.
have hs' : forall n, N (u n.+1-u n) <= t n-t n.+1.
  by move=> n; rewrite hstep; exact: hs.
have hb := @norm_increment_tail_bound R X N hN u t ht hs'.
apply: cauchy_exP=> e he.
have hcoef : 0 <= a/(1-c) by rewrite divr_ge0 //; exact: ltW hd.
have [k hk] := geometric_contraction_small hc hcoef he.
exists (u k : real_norm_metric_space hN); exists k=> // m hkm.
rewrite ballEmdist /=.
change (N (u k-u m) < e).
rewrite (real_seminorm_subtract hN.1).
apply: le_lt_trans (hb k m hkm) _.
by rewrite /t -mulrA.
Qed.

(** Source for [norm_geometric_increments_converge]: completeness
    supplies the limit of the iterates in Federer 3.1.1, p. 210, once
    the geometric increment bound is established. The target is a proved
    existential limit; no default limit point is introduced. *)
Theorem norm_geometric_increments_converge (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (u : nat -> X) (c a : R) :
  0 < c < 1 -> 0 <= a ->
  (forall n, N (u n.+1-u n) <= c^+n*a) ->
  exists z : real_norm_metric_space hN,
    (fun n => (u n : real_norm_metric_space hN)) @ \oo --> z.
Proof.
move=> hc ha hs.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter ((fun n => (u n : real_norm_metric_space hN)) @ \oo) :=
  @fmap_proper_filter nat (real_norm_metric_space hN) u \oo PF0.
exact: (@hcomplete _ PF (@norm_geometric_increments_cauchy R X N hN u c a hc ha hs)).
Qed.
