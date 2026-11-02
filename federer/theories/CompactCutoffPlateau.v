(** General-topology support for the partition of unity in Federer (1969),
    2.5.14, p. 108. A localized cutoff can be made equal to one on an open
    neighborhood of the compact set. It is derived here from the sealed
    cutoff laws by scaling and truncation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice CompactCutoffUP
  LocalizedCompactCutoffUP LocalizedCompactCutoff FunctionLatticeUP RealMetricBackground CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [localized_compact_cutoff_plateau]: the local plateau used
    for finite partitions in Federer 2.5.14, p. 108 The open plateau is
    contained in the prescribed open set because the whole support is
    contained there. *)
Lemma localized_compact_cutoff_plateau (R : realType) (X : topologicalType) (K V : set X) :
  hausdorff_space X -> locally_compact (@setT X) -> compact K -> open V -> K `<=` V ->
  exists (f : X -> R) O, is_localized_compact_cutoff K V f /\
    open O /\ K `<=` O /\ (forall x, O x -> f x= 1).
Proof.
move=> hh hl hK hV hKV.
pose u := @localized_compact_cutoff R X K V hh hl hK hV hKV.
have hu := @localized_compact_cutoff_specification R X K V hh hl hK hV hKV.
have hcut := localized_compact_cutoff_laws hu.
pose f x := Order.min (2*u x) 1.
pose O := [set x | (2 : R)^-1 < u x].
have hL := @compactly_supported_continuous_functions_lattice R X.
have huf : compactly_supported_continuous_functions u := compact_cutoff_function hcut.
have hff : compactly_supported_continuous_functions f.
  apply: (@function_lattice_truncation R X _ hL 1 (fun x => 2*u x) (@ler01 R)).
  apply: (@function_lattice_scale R X _ hL 2 u)=> //; by rewrite ler0n.
have hfone x : O x -> f x= 1.
  move=> hx; change (is_true ((2 : R)^-1 < u x)) in hx.
  have ht : 0 < (2 : R) by rewrite ltr0n.
  have hb : 1 < 2*u x by rewrite -(@ltr_pdivrMl R 2 (u x) 1 ht) mulr1.
  exact: min_idPr (ltW hb).
have hsupport : real_function_support f `<=` real_function_support u.
  apply: (@real_function_support_in_closed_set R X f _ (@real_function_support_closed R X u))=> x hx.
  by rewrite /f (real_function_zero_off_support hx) mulr0 (min_idPl (@ler01 R)).
exists f,O; split.
- constructor.
  + constructor=> //.
    * move=> x; have [h0 h1] := andP (compact_cutoff_range hcut x).
      apply/andP; split; last by rewrite /f ge_min lexx orbT.
      rewrite /f le_min ler01 andbT; exact: mulr_ge0 (ler0n R 2) h0.
    * move=> x hx; rewrite /f /u (compact_cutoff_on_set hcut hx) mulr1.
      apply: min_idPr; by rewrite ler1n.
  + move=> x hx; exact: (localized_compact_cutoff_support hu (hsupport x hx)).
- split.
  + exact ((@continuousP X (real_line_metric R) u).1 huf.1 _
      (@order_strict_upper_ray_open _ [the orderTopologicalType _ of R^o] (2 : R)^-1)).
  + split=> //; move=> x hx; change (is_true ((2 : R)^-1 < u x)).
    by rewrite /u (compact_cutoff_on_set hcut hx) invf_lt1 ?ltr0n // ltr1n.
Qed.
