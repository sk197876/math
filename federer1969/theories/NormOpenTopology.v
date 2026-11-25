(** Federer (1969), 4.1.1, pp. 344–345: connect a specified
    norm topology to the single-seminorm topology. This supporting
    adapter identifies the ordinary real scalar topology used in
    continuous real linear functionals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric OpenFamilyTopologyUP DirectedSeminormFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_open_family]: the ordinary given-norm
    topology, supporting the Banach source and target spaces and
    real scalar values in Federer 4.1.1, pp. 343–345. *)
Definition norm_open_family (R:realType) (E:lmodType R)
    (N:E->R) (hN:is_real_norm N):set (set E) :=
  fun A=>@open [the topologicalType of real_norm_metric_space hN] A.

(** Source for [norm_single_seminorm_directed]: a given norm
    is a one-member directed family of seminorms, supporting the
    continuity bounds of Federer 4.1.1, pp. 344–345. *)
Lemma norm_single_seminorm_directed (R:realType) (E:lmodType R)
    (N:E->R) (hN:is_real_norm N):
  is_directed_seminorm_family (fun _:unit=>N).
Proof.
constructor; [by exists tt|by move=>j; exact:hN.1|].
move=>i j; exists tt=>x; by split.
Qed.

(** Source for [norm_open_family_seminorm_laws]: the ordinary
    norm topology agrees with the independently specified
    seminorm-ball topology, supporting Federer 4.1.1, p. 344. *)
Theorem norm_open_family_seminorm_laws (R:realType) (E:lmodType R)
    (N:E->R) (hN:is_real_norm N):
  is_seminorm_family_topology (fun _:unit=>N) (norm_open_family hN).
Proof.
pose T := [the topologicalType of real_norm_metric_space hN].
split.
- constructor.
  + exact:(@openT T).
  + move=>A B; exact:(@openI T A B).
  + move=>I A hA; apply:bigcup_open=>i _; exact:hA i.
- move=>A; split.
  + move=>hA x hx.
    have hn:=@open_nbhs_nbhs T x A (conj hA hx).
    have [r hr hb]:=(metricType_numDomainType.nbhs_mdistP (x:T) A).1 hn.
    exists tt,r; split=>// y hy; apply:hb.
    change (is_true (N (x-y)<r)).
    by rewrite (real_seminorm_subtract hN.1).
  + move=>hA; rewrite /norm_open_family openE=>x hx.
    have [i [r [hr hb]]]:=hA x hx.
    apply:(metricType_numDomainType.nbhs_mdistP (x:T) A).2.
    exists r=>// y hy; apply:hb.
    change (is_true (N (y-x)<r)).
    by rewrite (real_seminorm_subtract hN.1).
Qed.
