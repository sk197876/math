(** Federer (1969), 3.1.16, p. 228: local Lipschitz regularity makes the
    intermediate map continuous and gives the order-zero growth hypothesis
    needed in 3.1.15. Only the abstract ball laws are used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import GrassmannAbbreviations Hom EuclideanInnerProduct
  InnerNorm InnerNormInequalities InnerMetric HilbertFormCompactness RealNormUP
  NormClassOneUP NormHigherDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearZero LipschitzUP MetricClosedBalls AnnularLipschitzExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Laws.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Variables (C : nat->set X) (f h : X->Y).
Hypothesis hh : is_annular_lipschitz_extension C f h.

(** Source for [annular_extension_local_increment]: the assertion that h
    is locally Lipschitzian in Federer 3.1.16, p. 228, expressed as a
    positive finite increment bound on a ball about each point. *)
Lemma annular_extension_local_increment (a : X) :
  exists M : R, 0<M /\ forall x : X, N (x-a)<1 -> NY (h x-h a)<=M*N (x-a).
Proof.
pose i := (Num.truncn (N a)).+2.
have /andP [_ htr] := truncn_itv (inner_norm_nonnegative (@euclidean_inner_productP R m) a).
have ha : N a<i%:R-1.
  by rewrite /i -natr1 addrK.
have [M [hM [hM0 hb]]] := annular_extension_ball_lipschitz hh i.
have hball x : N (x-a)<1 -> metric_closed_ball (0:X) (i%:R : R) x.
  move=>hx.
  have ht := inner_norm_triangle (@euclidean_inner_productP R m) (x-a) a.
  rewrite subrK in ht.
  change (is_true (mdist (0:X) x<=i%:R)).
  rewrite inner_metric_distanceE sub0r inner_normN; lra.
have haa : metric_closed_ball (0:X) (i%:R : R) a.
  apply: hball; by rewrite subrr inner_norm0 ltr01.
exists M; split=>// x hx.
have hbnd := hb x a (hball x hx) haa.
by rewrite !inner_metric_distanceE in hbnd.
Qed.

(** Source for [annular_extension_class_zero]: continuity of the
    intermediate locally Lipschitz map h in Federer 3.1.16, p. 228.
    The domain is the whole source space. *)
Lemma annular_extension_class_zero : norm_class_zero N NY (fun _=>True) h.
Proof.
move=>a _; split.
- exists 1; split; first exact: ltr01.
  by move=>v _.
- move=>e he; have [M [hM hb]] := annular_extension_local_increment a.
  exists (Num.min 1 (e/(M+1))); split; first by rewrite lt_min ltr01 divr_gt0 //; lra.
  move=>v _; rewrite lt_min=>/andP [hv1 hve].
  have hdiff : a+v-a=v by rewrite addrAC subrr add0r.
  have hbnd := hb (a+v); rewrite hdiff in hbnd.
  apply: le_lt_trans (hbnd hv1) _.
  have hv0 := inner_norm_nonnegative (@euclidean_inner_productP R m) v.
  have hlt : (M+1)*N v<e.
    have hMp : 0<M+1 by lra.
    by move: hve; rewrite (@ltr_pdivlMr R (M+1) _ _ hMp) mulrC.
  nra.
Qed.

(** Source for [annular_extension_zeroth_growth]: the use of k=0 in
    3.1.15 at the end of the proof of Federer 3.1.16, p. 228.
    Zeroth multilinear forms have exactly the norm of their values. *)
Lemma annular_extension_zeroth_growth
    (Z : nat->lmodType R) (ev : forall j, {ffun 'I_j->R_n R m}->Hom (Z j) (R_n R n))
    (ZN : forall j, Z j->R)
    (hZ : forall j, is_continuous_multilinear_space N NY (@ev j) (@ZN j)) :
  forall a : X, forall z, has_norm_higher_differential N ev ZN (fun _=>True) h 0%N a z ->
  exists M r : R, 0<r /\ forall x w,
    has_norm_higher_differential N ev ZN (fun _=>True) h 0%N x w ->
    N (x-a)<r -> @ZN 0%N (w-z)<=M*N (x-a).
Proof.
move=>a z [_ hz]; have [M [hM hb]] := annular_extension_local_increment a.
exists M, 1; split; first exact: ltr01.
move=>x w [_ hw] hx.
rewrite (continuous_multilinear_zero_norm (inner_norm_real_norm (@euclidean_inner_productP R n)) (@hZ 0%N)) linearB /= hw hz.
exact: hb x hx.
Qed.
End Laws.
