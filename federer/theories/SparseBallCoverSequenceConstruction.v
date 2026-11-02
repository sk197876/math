(** Federer (1969), 2.9.18(1), p. 163: the finite off-target covers and
    recursively separated radius sequence. The specification records the
    printed laws before selecting a witness. Natural index n denotes printed
    positive index n+1. General topology supplies the finite-subcover
    background. The measure-formula erratum issue is treated separately in
    WeightedHitMeasure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import SparseBallCoverSequenceUP FiniteOffTargetBallCover NowhereDenseUP
  MetricSetSeparationInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sparse_ball_cover_sequence_exists]: existence
    proof for the recursively chosen c_j and S_j in
    Federer 2.9.18(1), p. 163. Choose a
    finite off-target cover at each positive radius; its
    positive finite set-distance q supplies the next radius
    q/(j+1), strictly below q/j. This particular choice
    witnesses only the abstract sequence laws and is hidden
    behind the sealing module in subsequent developments. *)
Theorem sparse_ball_cover_sequence_exists (R : realType) (X : metricType R)
    (T : set X) : compact T -> is_nowhere_dense T -> T !=set0 ->
  exists c S, is_sparse_ball_cover_sequence T c S.
Proof.
move=> hT hnd hTn.
pose Stage (r : R) (S : set X) : Prop :=
  0<r /\ finite_set S /\ S `<=` ~` T /\
  (forall x, T x -> exists a, S a /\ mdist a x<r) /\
  (0<metric_set_distance_infimum S T<r%:E)%E.
have hex (r : R) (hr : 0<r) : exists S, Stage r S.
  have [S [hfinite [hoff [hcovers hsep]]]] := @finite_off_target_ball_cover R X T r hT hnd hTn hr.
  by exists S; split.
pose pick (r : R) (hr : 0<r) := cid (hex r hr).
pose State : Type := {r : R & {S : set X | Stage r S}}.
pose base : State := existT (fun r => {S : set X | Stage r S}) 1 (pick 1 (ltr01)).
have hstep (n : nat) (s : State) : exists t : State,
    (((n.+1)%:R*projT1 t)%R%:E<metric_set_distance_infimum (sval (projT2 s)) T)%E.
  pose r := projT1 s; pose S := sval (projT2 s).
  have hs : Stage r S := proj2_sig (projT2 s).
  have hsep := hs.2.2.2.2.
  have hsp : (0<metric_set_distance_infimum S T)%E := (andP hsep).1.
  have hsu : (metric_set_distance_infimum S T<r%:E)%E := (andP hsep).2.
  have hf : metric_set_distance_infimum S T \is a fin_num.
    rewrite (ge0_fin_numE (ltW hsp)); exact: lt_trans hsu (ltry r).
  pose q := fine (metric_set_distance_infimum S T).
  have heq : metric_set_distance_infimum S T=q%:E by rewrite /q fineK.
  have hq : 0<q by move: hsp; rewrite heq lte_fin.
  pose u := (q/((n.+2)%:R : R)).
  have hkp : 0<((n.+2)%:R : R) by rewrite ltr0n.
  have hu : 0<u by rewrite /u divr_gt0.
  pose t : State := existT (fun r => {S : set X | Stage r S}) u (pick u hu).
  exists t; change ((((n.+1)%:R*u)%R)%:E<metric_set_distance_infimum S T)%E.
  rewrite heq lte_fin /u mulrA (ltr_pdivrMr _ _ hkp).
  by rewrite [((n.+1)%:R : R)*q]mulrC (ltr_pM2l hq) ltr_nat.
pose step (n : nat) (s : State) := projT1 (cid (hstep n s)).
pose stages (n : nat) := nat_rect (fun _ => State) base step n.
pose c (n : nat) := projT1 (stages n).
pose S (n : nat) := sval (projT2 (stages n)).
have hs n : Stage (c n) (S n) := proj2_sig (projT2 (stages n)).
exists c,S; constructor.
- move=> n; exact: (hs n).1.
- by rewrite /c /stages /= /base.
- move=> n; exact: (hs n).2.1.
- move=> n; exact: (hs n).2.2.1.
- move=> n x hx; exact: (hs n).2.2.2.1 x hx.
- move=> n; exact: projT2 (cid (hstep n (stages n))).
- move=> n; exact: (andP (hs n).2.2.2.2).2.
Qed.
