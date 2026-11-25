(** Federer (1969), 3.4.10, p. 337:
    restrict the local analytic manifold pieces to
    the selected ambient open sets. Connect the
    existing regular-level characterization of 3.1.24,
    p. 240, to its existing open-domain laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormBoundedLinearTopology NormClassOneRestriction NormAnalyticUP NormAnalyticLocal
  NormAnalyticOperations AnalyticSubmanifoldUP AnalyticSubmanifoldChartsUP
  AnalyticSubmanifoldLevelSets AnalyticLevelStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_open_restriction]: the
    analytic version of the open restriction of
    3.1.19(1), p. 231, as prescribed in
    3.1.24, p. 240, and used for
    the manifold cover in 3.4.10, p. 337.
    Retain the existing analytic level functions and
    their actual differential fields. *)
Theorem analytic_submanifold_open_restriction (R:realType) n m
    (S U:set (R_n R n)):
  @is_euclidean_analytic_submanifold R n m S ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U ->
  @is_euclidean_analytic_submanifold R n m (S `&` U).
Proof.
move=>hS hU.
have hCharts:=analytic_submanifold_regular_level_charts hS.
apply:analytic_regular_level_charts_submanifold=>b [hbS hbU].
have [i [V [f [D [hVb [hMN [hNI [hF [hD [hLevel hRank]]]]]]]]]]:=hCharts b hbS.
pose X:=R_n R n;pose Y:=R_n R i.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R i).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R i).
pose W:=V `&` U.
have hVOpen:=norm_analytic_domain_open hF.
have hWOpen:@open (real_norm_metric_space hNX) W:=openI hVOpen hU.
have hInterior x (hx:W x):norm_domain_interior NX W x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  have h:=hWOpen;rewrite openE in h;exact:h x hx.
have hbV:V b:=norm_domain_interior_member hNX hVb.
exists i,W,f,D;split;first exact:hInterior b (conj hbV hbU).
split;first exact:hMN.
split;first exact:hNI.
split.
- exact:(@norm_analytic_open_restriction R X Y NX NY hNX hNY V W f
    (fun x hx=>hx.1) hInterior hF).
split.
- exact:(@norm_class_one_field_open_restriction R X Y NX NY V W f D
    (fun x hx=>hx.1) hInterior hD).
split;last by move=>x hx;exact:hRank x hx.1.
apply/seteqP;split.
- move=>x [[hxS hxU] [hxV _]];split;first by split.
  have h:(S `&` V) x by split.
  by rewrite hLevel in h;exact:h.2.
- move=>x [[hxV hxU] hZero];split;last by split.
  split;last exact:hxU.
  have h:(S `&` V) x by rewrite hLevel;split.
  exact:h.1.
Qed.
