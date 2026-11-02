(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import SparseBallCoverSequenceUP ExtendedRealReciprocalBounds RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sparse_cover_radii_decreasing]: supporting
    decrease of the radii in Federer 2.9.18(1),
    p. 163. The printed separation inequalities imply
    (n+1)c_(n+1)<c_n and hence c_(n+1)<c_n. *)
Lemma sparse_cover_radii_decreasing (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n, c n.+1<c n.
Proof.
move=> h n.
have hh := lt_trans (sparse_cover_separation_lower h n) (sparse_cover_separation_upper h n).
rewrite lte_fin in hh.
have hmul : c n.+1<=((n.+1)%:R : R)*c n.+1.
  have hn : (1<=((n.+1)%:R : R)) by rewrite ler1n.
  have hm := ler_wpM2r (ltW (sparse_cover_radius_positive h n.+1)) hn.
  by rewrite mul1r in hm.
exact: le_lt_trans hmul hh.
Qed.

(** Source for [sparse_cover_radii_le_one]: supporting uniform
    coefficient bound in the weighted-hit measure of Federer
    2.9.18(1), p. 163. Positive decreasing
    radii beginning at one never exceed one. *)
Lemma sparse_cover_radii_le_one (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n, c n<=1.
Proof.
move=> h; elim=> [|n ih]; first by rewrite (sparse_cover_initial_radius h).
exact: le_trans (ltW (sparse_cover_radii_decreasing h n)) ih.
Qed.

(** Source for [sparse_cover_reciprocal_bound]: supporting
    decay estimate in Federer 2.9.18(1), p. 163.
    The separation condition bounds the next radius strictly
    below 1/(n+1), independently of a particular recursive witness. *)
Lemma sparse_cover_reciprocal_bound (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n,
    c n.+1<(((n.+1)%:R : R)^-1).
Proof.
move=> h n.
have hh := lt_trans (sparse_cover_separation_lower h n) (sparse_cover_separation_upper h n).
rewrite lte_fin in hh.
have hb := lt_le_trans hh (sparse_cover_radii_le_one h n).
have hk : 0<((n.+1)%:R : R) by rewrite ltr0n.
have hk0 : ((n.+1)%:R : R)!=0 by rewrite (gt_eqF hk).
have he : ((n.+1)%:R : R)*(((n.+1)%:R : R)^-1)= 1 by rewrite mulfV.
have hm : ((n.+1)%:R : R)*c n.+1<((n.+1)%:R : R)*(((n.+1)%:R : R)^-1).
  by rewrite he.
by move: hm; rewrite (ltr_pM2l hk).
Qed.

(** Source for [sparse_cover_radii_tend_zero]: supporting
    convergence c_j to zero used in both oscillating-radius
    comparisons of Federer 2.9.18(1), p. 163.
    The reciprocal bound gives an explicit eventual estimate
    for every positive epsilon. *)
Lemma sparse_cover_radii_tend_zero (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall e : R, 0<e ->
  exists N, forall n, (N<=n)%N -> c n<e.
Proof.
move=> h e he; have [N hN] := positive_reciprocal_nat_small he.
exists N.+1; move=> [|n] hn; first by rewrite leqn0 in hn.
apply: lt_trans (sparse_cover_reciprocal_bound h n) _.
apply: le_lt_trans (@positive_reciprocal_nat_antitone R N n _) hN.
exact: hn.
Qed.

(** Source for [sparse_cover_radii_antitone]: supporting
    comparison of all later coefficients in Federer 2.9.18(1),
    p. 163. Successive strict decrease implies that
    later radii are at most any earlier radius. *)
Lemma sparse_cover_radii_antitone (R : realType) (X : metricType R)
    (T : set X) (c : nat -> R) (S : nat -> set X) :
  is_sparse_ball_cover_sequence T c S -> forall n m, (n<=m)%N -> c m<=c n.
Proof.
move=> h n m hnm.
have hall k : c (n+k)%N<=c n.
  elim: k=> [|k ih]; first by rewrite addn0.
  rewrite addnS; exact: le_trans (ltW (sparse_cover_radii_decreasing h (n+k))) ih.
have he : (n+(m-n)=m)%N by rewrite addnC subnK.
by rewrite -he; exact: hall (m-n)%N.
Qed.
