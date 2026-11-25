(** Federer (1969), 2.10.28(3), p. 192: supporting uniform small-set bound
    for a finite open interval cover of a compact set. Here use the sum of
    the finitely many nonnegative endpoint margins instead; a positive
    uniform margin follows by the same compact extreme-value argument. All
    topology and finite-sum tools are background. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground StieltjesCaratheodoryUP CompactMaximum MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_interval_cover_small_sets]: supporting positive
    scale epsilon in the lower-bound proof of 2.10.28(3), p. 192 Any set
    meeting the covered compact set with sufficiently small diameter lies in
    one covering interval. Empty compact sets, repeated covering intervals
    and zero-diameter small sets are included. *)
Theorem compact_interval_cover_small_sets (R : realType) (I : choiceType)
    (F : {fset I}) (U : I -> stieltjes_open_intervals R) (C : set (real_line_metric R)) :
  compact C -> C `<=` \bigcup_(i in [set` F]) stieltjes_interval_set (U i) ->
  exists e : R, 0<e /\ forall S : set (real_line_metric R),
    C `&` S !=set0 -> (@extended_metric_diameter R [the metricType R of real_line_metric R] S<=e%:E)%E ->
    exists i, i \in F /\ S `<=` stieltjes_interval_set (U i).
Proof.
move=> hC hcover; case: (pselect (C !=set0))=> hne; last first.
  exists 1; split; first exact: ltr01.
  move=> S [x [hxC hxS]] hsize; exfalso; apply: hne; by exists x.
pose margin (i : I) (x : real_line_metric R) :=
  Order.max 0 (Order.min (x-(val (U i)).1) ((val (U i)).2-x)).
have hm0 (i : I) (x : real_line_metric R) : 0<=margin i x by rewrite /margin le_max lexx.
have hmc (i : I) : continuous (margin i : real_line_metric R -> R^o).
  move=> x; apply: (@continuous_max R (real_line_metric R) (fun _=>0)
    (fun y=>Order.min (y-(val (U i)).1) ((val (U i)).2-y)) x); first exact: cvg_cst.
  apply: (@continuous_min R (real_line_metric R) (fun y=>y-(val (U i)).1) (fun y=>(val (U i)).2-y) x).
  - apply: (@continuousB R R^o (real_line_metric R) (fun y=>y) (fun _=>(val (U i)).1) x);
      [exact: cvg_id | exact: cvg_cst].
  - apply: (@continuousB R R^o (real_line_metric R) (fun _=>(val (U i)).2) (fun y=>y) x);
      [exact: cvg_cst | exact: cvg_id].
pose g (x : real_line_metric R) := \sum_(i <- F) margin i x.
have hgc : continuous (g : real_line_metric R -> R^o).
  apply: continuous_big; first exact: add_continuous.
  by move=> i _; exact: hmc.
have hgp (x : real_line_metric R) (hx : C x) : 0<g x.
  have [i hi hxi] := hcover x hx.
  have /andP[hl hr] : (val (U i)).1<x< (val (U i)).2.
    by move: hxi; rewrite /stieltjes_interval_set /= in_itv.
  have hmi : 0<margin i x by rewrite /margin lt_max ltxx /= lt_min !subr_gt0 hl hr.
  have hrest : 0<=\sum_(j <- (F `\ i)%fset) margin j x.
    apply: sumr_ge0=> j _; exact: hm0.
  rewrite /g (big_fsetD1 _ hi) /=; lra.
have hnegc : continuous (fun x : real_line_metric R=>(-g x : R^o)).
  move=> x; exact: continuousN (hgc x).
have [x0 [hx0 hmax]] := @continuous_compact_maximum R (real_line_metric R) C (fun x=>(-g x : R^o)) hne hC hnegc.
pose m := g x0.
have hm : 0<m := hgp x0 hx0.
have hmin (x : real_line_metric R) (hx : C x) : m<=g x.
  have hh := hmax x hx; by rewrite lerN2 in hh.
pose N := \sum_(i <- F) (1 : R).
have hN0 : 0<=N by apply: sumr_ge0=> i _; exact: ler01.
have hNp : 0<N+1 by lra.
pose e := m/(N+1).
have he : 0<e by rewrite /e divr_gt0.
have htotal : (N+1)*e=m by rewrite /e mulrC divfK ?gt_eqF.
have hNe : N*e<m by lra.
have hconst : (\sum_(i <- F) e)=N*e.
  rewrite /N mulr_suml; apply: eq_big_seq=> i _; by rewrite mul1r.
exists e; split=> // S [x [hxC hxS]] hsize.
have hchoice : exists i, i \in F /\ e<margin i x.
  apply: contrapT=> hnone.
  have hall i (hi : i \in F) : margin i x<=e.
    rewrite leNgt; apply/negP=> hh; apply: hnone; exists i; by split.
  have hupper : g x<=N*e.
    rewrite -hconst /g !big_seq; apply: ler_sum=> i hi; exact: hall.
  have hh := le_trans (hmin x hxC) hupper.
  by have hf := lt_le_trans hNe hh; rewrite ltxx in hf.
have [i [hi hmi]] := hchoice.
have hmargin : e<Order.min (x-(val (U i)).1) ((val (U i)).2-x).
  move: hmi; rewrite /margin lt_max=> /orP [he0|hmi]; last exact hmi.
  by have hh := lt_trans he he0; rewrite ltxx in hh.
have [hleft hright] : e<x-(val (U i)).1 /\ e<(val (U i)).2-x.
  by move: hmargin; rewrite lt_min=> /andP [h1 h2]; split.
exists i; split=> // y hy.
have hd := @metric_diameter_upper R [the metricType R of real_line_metric R] S _
  (extended_metric_diameter_specification S) y x hy hxS.
have hyx : `|y-x|<=e.
  have hh := le_trans hd hsize; by rewrite real_line_metric_distanceE lee_fin in hh.
move: hyx; rewrite ler_norml=> /andP[hlo hhi].
rewrite /stieltjes_interval_set /= in_itv /=; apply/andP; split; lra.
Qed.
