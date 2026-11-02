(** General-topology existence proof supporting Federer (1969), 2.5.13, p.
    106, and 2.5.14, p. 107: a compact set in a locally compact Hausdorff
    space has a continuous compactly supported cutoff. We use Urysohn
    separation in the one-point compactification and truncate away a
    neighborhood of the extra point. The narrow Urysohn import supplies
    general topology, not an external representation or integration theorem.
    The witness is private; downstream mathematics uses the sealed cutoff
    laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import urysohn normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactCutoffUP CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_cutoff_exists]: existence of the cutoff required by
    Federer 2.5.13, p. 106 Local compactness and Hausdorff separation ensure
    that the one-point compactification is compact Hausdorff, so Urysohn's
    general-topology lemma applies. The conclusion includes empty K and an
    empty ambient space. *)
Theorem compact_cutoff_exists (R : realType) (X : topologicalType) (K : set X) :
  hausdorff_space X -> locally_compact (@setT X) -> compact K ->
  exists f : X -> R, is_compact_cutoff K f.
Proof.
move=> hh hl hK.
pose T := [the topologicalType of one_point_compactification X].
have hT : hausdorff_space T := one_point_compactification_hausdorff hl hh.
have hnorm : normal_space T := compact_normal hT one_point_compactification_compact.
have hemb : continuous (Some : X -> T) := one_point_compactification_some_continuous.
have hKC : compact (Some @` K : set T).
  apply: continuous_compact _ hK; exact: continuous_subspaceT hemb.
have hcK : closed (Some @` K : set T) := compact_closed hT hKC.
have hcN : closed ([set None] : set T) := compact_closed hT (@compact_set1 T None).
have hdis : ([set None] : set T) `&` (Some @` K) = set0.
  apply/seteqP; split=> [p [-> [x _ hx]]|p []]; by [].
have hsep := (@normal_separatorP R T).1 hnorm [set None] (Some @` K) hcN hcK hdis.
have [u [hu h01 h0 h1]] := (@uniform_separatorP T R [set None] (Some @` K)).1 hsep.
have hu0 : u None= 0 by apply: h0; exists None.
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
exists f; constructor; first by split.
- move=> x; apply/andP; split.
  + rewrite /f le_min ler01 le_max lexx; by [].
  + by rewrite /f ge_min lexx.
- move=> x hx; rewrite /f /w (hu1 x hx) addrK (max_idPr (@ler01 R)); exact: minxx.
Qed.
