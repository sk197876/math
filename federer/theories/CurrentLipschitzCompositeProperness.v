(** Federer (1969), 4.1.14, p. 371: properness of
    g composed with f on the original current support
    supplies the separate properness in the composition law.
    The topological argument of 4.1.7, p. 359, needs
    only continuity. No selected smooth image, whole-domain
    properness or normality is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentProperSupport CurrentProperSupportDomain CurrentSupportMapTopology
  SmoothFormPullbackComposition FunctionalSupportRelativeClosed ProperMapUP
  ProperMapComposition ProperSmallerClosedSubset IsotropyGroupTopology
  SubtypeCompactHausdorff SmoothCompactSet SmoothCompactImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentLipschitzCompositeProperness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n q m:nat.
Local Notation X:=(R_n R v).
Local Notation Y:=(R_n R n).
Local Notation Z:=(R_n R q).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R q)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R q)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Arguments hFImage : clear implicits.
Hypothesis hGImage:forall y,V y->W (g y).
Arguments hGImage : clear implicits.
Hypothesis hf:norm_class_zero NX NY U f.
Hypothesis hg:norm_class_zero NY NZ V g.
Variable T:@current_space R h2 v U hU m.
Local Notation support:=(@current_support R h2 v U hU m T).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Local Notation VT:=(current_domain R n V).
Local Notation WT:=(current_domain R q W).
Local Notation ST:=[the topologicalType of set_type (support:set XT)].
Local Notation fS:=(@current_map_on_support R h2 v n m U hU V T f hFImage).
Local Notation gV:=(@current_map_on_domain R n q V W g hGImage).
Local Notation hGFImage:=(@current_smooth_composite_image R v n q U V W f g hFImage hGImage).
Hypothesis hpGF:@is_current_proper_on_support R h2 v q m U hU W T
  (fun x=>g (f x)) hGFImage.

(** Source for [current_lipschitz_composite_support_properness]:
    f is proper on sptT and g on the full f(sptT),
    supporting the original locally Lipschitz composition
    formula of Federer 4.1.14, p. 371. The proof
    uses the preceding topological composition laws only. *)
Theorem current_lipschitz_composite_support_properness:
  @is_current_proper_on_support R h2 v n m U hU V T f hFImage /\
  is_proper_map (fun y:set_type (fS @` setT)=>gV (set_val y)).
Proof.
have hF:continuous fS:=@current_support_map_continuous R h2 v n m U hU V
  T f hFImage hf.
have hG:=@current_map_on_domain_continuous R n q V W g hGImage hg.
have hEqual:gV \o fS=@current_map_on_support R h2 v q m U hU W T
    (fun x=>g (f x)) hGFImage.
  apply:funext=>x;apply:val_inj;by [].
have hComposite:is_proper_map (gV \o fS) by rewrite hEqual;exact:hpGF.
have hHausdorff:hausdorff_space VT.
  exact:(@set_type_hausdorff YT V (@metric_hausdorff R YT)).
split.
- exact:(@proper_composite_first ST VT WT fS gV hHausdorff hF hG hComposite).
- exact:(@proper_composite_on_image ST VT WT fS gV hF hComposite).
Qed.

(** Source for [current_lipschitz_composite_current_support_proper]:
    g is proper on the support of every current Q
    whose support lies in f(sptT), supporting Federer
    4.1.14, p. 371. Q need not be a selected
    image, representable, normal or of the degree of T. *)
Theorem current_lipschitz_composite_current_support_proper d
    (Q:@current_space R h2 n V hV d):
  @current_support R h2 n V hV d Q `<=` f @` support->
  @is_current_proper_on_support R h2 n q d V hV W Q g hGImage.
Proof.
move=>hSupportImage.
pose A:set VT:=[set y|@current_support R h2 n V hV d Q (set_val y)].
pose B:set VT:=fS @` setT.
have[C [hC hSupport]]:=@functional_support_relative_closed R Y (A_m Y R^o d) NY hNY V
  (@current_test_space R h2 n V hV d) (@current_test_value R h2 n V hV d)
  (@current_value R h2 n V hV d Q).
have hActual:@current_support R h2 n V hV d Q=V `&` C:=hSupport.
have hEqual:A=(set_val @^-1` C:set VT).
  apply:funext=>y;apply:propext;split.
  - move=>hy;have hVC:(V `&` C) (set_val y) by rewrite -hActual;exact:hy.
    exact:hVC.2.
  - move=>hy;rewrite /A hActual;exact:conj (set_valP y) hy.
have hClosed:closed A.
  rewrite hEqual.
  apply:(@preimage_closed [the topologicalType of VT] [the topologicalType of YT]
    (fun y:VT=>(set_val y:YT)) C _ hC).
  by move=>y _;exact:(@set_type_val_continuous YT V y).
have hAB:A `<=` B.
  move=>y hy.
  have[x hx hFx]:=@hSupportImage (set_val y) hy.
  exists (exist _ x (mem_set hx));first by [].
  apply:val_inj;exact:hFx.
have hImageProper:=current_lipschitz_composite_support_properness.2.
have hNested:=@proper_map_smaller_closed_subset VT WT gV A B hClosed hAB hImageProper.
exact:(@current_domain_support_proper_reverse R h2 n q V W g hGImage d hV Q hNested).
Qed.

(** Source for [current_lipschitz_composite_compact_loci]:
    over every compact target set, the original source
    locus in sptT and its full intermediate image are
    compact, supporting the cutoff in the composition proof
    of Federer 4.1.14, p. 371. Empty loci are allowed. *)
Theorem current_lipschitz_composite_compact_loci (C:set WT):
  compact C->
  compact ((gV \o fS) @^-1` C) /\
  compact ((fun x:ST=>(set_val x:XT)) @` ((gV \o fS) @^-1` C)) /\
  compact (fS @` ((gV \o fS) @^-1` C)).
Proof.
move=>hC.
have hEqual:gV \o fS=@current_map_on_support R h2 v q m U hU W T
    (fun x=>g (f x)) hGFImage.
  apply:funext=>x;apply:val_inj;by [].
have hComposite:is_proper_map (gV \o fS) by rewrite hEqual;exact:hpGF.
have hSource:=hComposite C hC.
split;first exact:hSource.
split.
- apply:continuous_compact hSource;apply:continuous_subspaceT.
  exact:(@set_type_val_continuous XT support).
- apply:continuous_compact hSource;apply:continuous_subspaceT.
  exact:(@current_support_map_continuous R h2 v n m U hU V T f hFImage hf).
Qed.

(** Source for [current_lipschitz_composite_full_image_compact_locus]:
    a compact target set has a compact intermediate
    locus containing every f(x) with x in sptT
    and g(f(x)) in that target set, supporting
    the original composition proof in Federer 4.1.14,
    p. 371. The preceding support-proper compact preimage
    and continuous compact image give the locus directly.
    Cancellation in the current image is irrelevant. *)
Theorem current_lipschitz_composite_full_image_compact_locus
    (C:smooth_compact_set hNZ W):
  exists L:smooth_compact_set hNY V,
    forall x,support x->smooth_compact_carrier C (g (f x))->
      smooth_compact_carrier L (f x).
Proof.
pose sourceLocus:=@current_proper_support_compact_locus R h2 v q m
  U hU W T (fun x=>g (f x)) hGFImage hpGF C.
pose L:=@smooth_compact_image R X Y NX NY hNX hNY
  U V f hFImage hf sourceLocus.
exists L=>x hx hCx.
change ((f @` [set z|support z /\smooth_compact_carrier C (g (f z))]) (f x)).
exists x;first exact:conj hx hCx.
by [].
Qed.

(** Source for [current_lipschitz_composite_full_image_compact_locus_values]:
    the same compact locus applies to the whole
    original image f(sptT), supporting Federer 4.1.14,
    p. 371, without a support equality for f#T. *)
Theorem current_lipschitz_composite_full_image_compact_locus_values
    (C:smooth_compact_set hNZ W):
  exists L:smooth_compact_set hNY V,
    forall y,(f @` support) y->smooth_compact_carrier C (g y)->
      smooth_compact_carrier L y.
Proof.
have[L hL]:=current_lipschitz_composite_full_image_compact_locus C.
exists L=>y [x hx <-] hCx.
exact:(@hL x hx hCx).
Qed.
End CurrentLipschitzCompositeProperness.
