(** Private general-topology construction supporting Federer (1969), 2.5.14,
    p. 108, first display. We construct it by induction on the finite cover:
    a localized plateau handles the portion outside the other open sets, and
    multiplication by its complement modifies the remaining partition. No
    external partition-of-unity theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportProducts CompactCutoffUP LocalizedCompactCutoffUP CompactCutoffPlateau FiniteCompactPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_compact_partition_exists]: existence of the g_n in
    Federer 2.5.14, p. 108 The compact set and the finite cover may be
    empty. Each original cover index receives one function, so repeated
    cover costs are not introduced. *)
Theorem finite_compact_partition_exists (R : realType) (X : topologicalType) (J : choiceType)
    (V : J -> set X) : hausdorff_space X -> locally_compact (@setT X) ->
  forall (F : {fset J}) K, compact K -> (forall j, j \in F -> open (V j)) ->
  K `<=` \bigcup_(j in [set` F]) V j -> exists g : J -> X -> R, is_finite_compact_partition V F K g.
Proof.
move=> hh hl; elim/fset1U_rect=> [|j F hj IH] K hK hV hcov.
- exists (fun _ _ => (0 : R)); constructor.
  + by move=> i; rewrite in_fset0.
  + by move=> i; rewrite in_fset0.
  + by move=> i; rewrite in_fset0.
  + move=> x hx; have [i hi _] := hcov x hx.
    change (is_true (i \in (fset0 : {fset J}))) in hi; by move: hi; rewrite in_fset0.
- pose U := \bigcup_(i in [set` F]) V i.
  have hVF i : i \in F -> open (V i).
    move=> hi; apply: hV; by rewrite !inE hi orbT.
  have hoU : open U by apply: bigcup_open=> i hi; exact: hVF hi.
  have hcK : closed K := compact_closed hh hK.
  have hK0 : compact (K `\` U).
    apply: (@subclosed_compact X _ K _ hK); last by move=> x [hx _].
    apply: closedI=> //; by rewrite closedC.
  have hKj : K `\` U `<=` V j.
    move=> x [hx hnx]; have [i hi hxi] := hcov x hx.
    change (is_true (i \in (j |` F)%fset)) in hi.
    move: hi; rewrite in_fset1U=> /orP[/eqP hij|hi]; first by rewrite -hij.
    exfalso; apply: hnx; by exists i.
  have hoVj : open (V j) by apply: hV; rewrite in_fset1U eqxx.
  have [f [O [hf [hoO [hKO hfO]]]]] := @localized_compact_cutoff_plateau R X (K `\` U) (V j) hh hl hK0 hoVj hKj.
  have hcut := localized_compact_cutoff_laws hf.
  have hff := compact_cutoff_function hcut.
  have hK' : compact (K `\` O).
    apply: (@subclosed_compact X _ K _ hK); last by move=> x [hx _].
    apply: closedI=> //; by rewrite closedC.
  have hcov' : K `\` O `<=` U.
    move=> x [hx hnO]; apply: contrapT=> hnU; apply: hnO; apply: hKO; by split.
  have [h hp] := IH (K `\` O) hK' hVF hcov'.
  pose g i x := if i==j then f x else (1-f x)*h i x.
  have hgj : g j=f by apply: funext=> x; rewrite /g eqxx.
  have hgi i : i \in F -> g i=(fun x => (1-f x)*h i x).
    move=> hi; apply: funext=> x; rewrite /g; case: eqP=> // hij.
    by move: hj; rewrite -hij hi.
  have hcomp : continuous (fun x : X => (1-f x) : real_line_metric R).
    move=> x; exact (@continuousB R R^o X (fun _ => 1) f x (cvg_cst _) (hff.1 x)).
  exists g; constructor.
  + move=> i; rewrite in_fset1U=> /orP[/eqP ->|hi]; first by rewrite hgj.
    rewrite (hgi i hi); apply: compact_support_continuous_multiplier hcomp _.
    exact: ((@finite_compact_partition_functions R X J V F (K `\` O) h hp i hi)).
  + move=> i; rewrite in_fset1U=> /orP[/eqP ->|hi] x.
    * rewrite hgj; exact: compact_cutoff_range hcut x.
    * rewrite (hgi i hi); apply: unit_interval_complement_product (compact_cutoff_range hcut x) _.
      exact: ((@finite_compact_partition_range R X J V F (K `\` O) h hp i hi) x).
  + move=> i; rewrite in_fset1U=> /orP[/eqP ->|hi].
    * rewrite hgj; exact: localized_compact_cutoff_support hf.
    * rewrite (hgi i hi); move=> x hx; apply: ((@finite_compact_partition_support R X J V F (K `\` O) h hp i hi)).
      exact: (real_product_support_right hx).
  + move=> x hx; rewrite big_fsetU1 // hgj.
    have he : (\sum_(i <- F) g i x)=(1-f x)*\sum_(i <- F) h i x.
      rewrite mulr_sumr !big_seq; apply: eq_bigr=> i hi; by rewrite (hgi i hi).
    rewrite he.
    change (f x+(1-f x)*\sum_(i <- F) h i x= 1).
    case: (pselect (O x))=> hOx.
    * by rewrite (hfO x hOx) subrr mul0r addr0.
    * have hxK : (K `\` O) x by split.
      rewrite (@finite_compact_partition_sum R X J V F (K `\` O) h hp x hxK) mulr1 addrCA subrr addr0.
      exact: erefl.
Qed.
