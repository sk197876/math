(** General topology supporting Federer (1969), 3.1.23,
    p. 237: a real normed vector space is connected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets set_interval reals topology normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_norm_space_connected]: connectedness used
    in the final open-and-closed image argument of Federer
    3.1.23, p. 237. The normed space is the union
    of its radial segments, all meeting at zero; their connectedness
    follows from the real interval and scalar-orbit continuity. *)
Lemma real_norm_space_connected (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) :
  @connected (real_norm_metric_space hN) setT.
Proof.
pose M:=real_norm_metric_space hN.
pose P (x:M):set M:=(fun t:real_line_metric R=>t*:x) @` `[0,1].
have hP x:connected (P x).
  apply: connected_continuous_connected; first exact: segment_connected.
  apply: continuous_subspaceT=>t; exact: real_norm_metric_scalar_orbit_continuous.
have h0:(\bigcap_(x in @setT M) P x)!=set0.
  exists 0=>x _; exists (0:R); last by rewrite scale0r.
  by rewrite set_itvcc /= lexx ler01.
have heq:(@setT M)=\bigcup_(x in @setT M) P x.
  apply/seteqP; split=>x _; last exact Logic.I.
  exists x; first exact Logic.I.
  exists (1:R); last by rewrite scale1r.
  by rewrite set_itvcc /= ler01 lexx.
rewrite heq; exact (bigcup_connected h0 (fun x _=>hP x)).
Qed.
