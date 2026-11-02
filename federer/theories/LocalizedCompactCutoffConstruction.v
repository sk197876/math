(** General-topology existence proof supporting Federer (1969), 2.5.14, pp.
    107–108: a compact set in a locally compact Hausdorff space has a
    continuous compactly supported cutoff. We use Urysohn separation in the
    one-point compactification and truncate away the prescribed closed
    complement and a neighborhood of the extra point. The narrow Urysohn
    import supplies general topology, not an external representation or
    integration theorem. The witness is private; downstream mathematics uses
    the sealed cutoff laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import urysohn normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactCutoffUP LocalizedCompactCutoffUP CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [localized_compact_cutoff_exists]: general-topology existence
    of functions with support in a prescribed open set, used in Federer
    2.5.14, pp. 107–108 Separate the compact set from the complement of its
    open neighborhood in the one-point compactification, then truncate below
    a positive level. This is not an additional representation theorem. *)
Theorem localized_compact_cutoff_exists (R : realType) (X : topologicalType) (K V : set X) :
  hausdorff_space X -> locally_compact (@setT X) -> compact K -> open V -> K `<=` V ->
  exists f : X -> R, is_localized_compact_cutoff K V f.
Proof.
move=> hh hl hK hV hKV.
pose T := [the topologicalType of one_point_compactification X].
have hT : hausdorff_space T := one_point_compactification_hausdorff hl hh.
have hnorm : normal_space T := compact_normal hT one_point_compactification_compact.
have hemb : continuous (Some : X -> T) := one_point_compactification_some_continuous.
have hKC : compact (Some @` K : set T).
  apply: continuous_compact _ hK; exact: continuous_subspaceT hemb.
have hcK : closed (Some @` K : set T) := compact_closed hT hKC.
pose D := ~` (Some @` V : set T).
have hcD : closed D by rewrite /D closedC; exact: one_point_compactification_open_some hV.
have hdis : D `&` (Some @` K) = set0.
  apply/seteqP; split=> [p [hp [x hx he]]|p []].
  apply: hp; exists x; [exact (hKV x hx)|exact he].
have hsep := (@normal_separatorP R T).1 hnorm D (Some @` K) hcD hcK hdis.
have [u [hu h01 h0 h1]] := (@uniform_separatorP T R D (Some @` K)).1 hsep.
have huD p : D p -> u p= 0 by move=> hp; apply: h0; exists p.
have hu0 : u None= 0 by apply: huD=> -[x _ hx].
have hu1 x : K x -> u (Some x)= 1.
  move=> hx; apply: h1; exists (Some x)=> //; by exists x.
pose w p := u p+u p.
have hw : continuous w by move=> p; exact: (@continuousD R R^o T u u p (hu p) (hu p)).
have hU : @nbhs T T None [set p | w p < 1].
  have hnb : nbhs (w None) [set r | r < (1 : R)].
    have hw0 : w None= 0 by rewrite /w hu0 add0r.
    rewrite hw0; apply: open_nbhs_nbhs; split; first exact: order_strict_lower_ray_open.
    exact: ltr01.
  exact (hw None _ hnb).
have [C [hC hcC] hCU] := hU.
pose f x := Order.min 1 (Order.max 0 (w (Some x)-1)).
have hf : continuous (f : X -> real_line_metric R).
  move=> x; apply: (@continuous_min R X (fun _ => 1) (fun x => Order.max 0 (w (Some x)-1)) x); first exact: cvg_cst.
  apply: (@continuous_max R X (fun _ => 0) (fun x => w (Some x)-1) x); first exact: cvg_cst.
  apply: (@continuousB R R^o X (fun x => w (Some x)) (fun _ => 1) x); last exact: cvg_cst.
  exact (@continuous_comp X T R^o Some w x (hemb x) (hw (Some x))).
have hfc : compact (real_function_support f).
  apply: (@real_function_compact_support_in_closed_set R X f C hC hcC)=> x hx.
  have hhx : w (Some x)<1 by apply: hCU; left; by exists x.
  have hneg : w (Some x)-1 <= 0 by rewrite subr_le0; exact: ltW hhx.
  by rewrite /f (max_idPl hneg) (min_idPr (@ler01 R)).
have hsupport : real_function_support f `<=` V.
  have hclosed : closed [set x | 1 <= w (Some x)].
    have hwX : continuous (fun x : X => w (Some x)).
      move=> x; exact (@continuous_comp X T R^o Some w x (hemb x) (hw (Some x))).
    exact ((@continuous_closedP X R^o (fun x => w (Some x))).1 hwX _
      (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] 1)).
  have hsub : real_function_support f `<=` [set x | 1 <= w (Some x)].
    apply: (@real_function_support_in_closed_set R X f _ hclosed)=> x hx.
    have hwlt : w (Some x)<1 by rewrite ltNge; apply/negP; exact hx.
    have hn : w (Some x)-1 <= 0 by rewrite subr_le0; exact: ltW hwlt.
    by rewrite /f (max_idPl hn) (min_idPr (@ler01 R)).
  move=> x hx; apply: contrapT=> hxV.
  have hDx : D (Some x) by move=> [y hy [he]]; apply: hxV; by rewrite -he.
  have hb := hsub x hx; change (is_true (1 <= w (Some x))) in hb.
  by move: hb; rewrite /w (huD _ hDx) add0r ler10.
exists f; constructor=> //; constructor; first by split.
- move=> x; apply/andP; split.
  + rewrite /f le_min ler01 le_max lexx; by [].
  + by rewrite /f ge_min lexx.
- move=> x hx; rewrite /f /w (hu1 x hx) addrK (max_idPr (@ler01 R)); exact: minxx.
Qed.
