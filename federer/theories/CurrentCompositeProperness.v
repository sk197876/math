(** Federer (1969), 4.1.7, p. 359:
    properness of g composed with f on
    the original spt T implies every
    separate properness needed in the printed
    composition formula. No whole-domain properness
    assumption on either map is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentProperSupport CurrentProperSupportDomain CurrentSupportMapTopology CurrentPushforwardSealed
  CurrentPushforwardSupport SmoothFormPullbackComposition FunctionalSupportRelativeClosed ProperMapUP
  ProperMapComposition ProperSmallerClosedSubset IsotropyGroupTopology SubtypeCompactHausdorff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompositeProperness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n q m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R q).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R q)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R q)).
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
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNY hNZ V g.
Variable T:@current_space R h2 v U hU m.
Local Notation support := (@current_support R h2 v U hU m T).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Local Notation VT := (current_domain R n V).
Local Notation WT := (current_domain R q W).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation fS := (@current_map_on_support R h2 v n m U hU V T f hFImage).
Local Notation gV := (@current_map_on_domain R n q V W g hGImage).
Local Notation hGFImage := (@current_smooth_composite_image R v n q U V W f g hFImage hGImage).
Hypothesis hpGF:@is_current_proper_on_support R h2 v q m U hU W T (fun x=>g (f x)) hGFImage.

(** Source for [current_composite_support_properness]:
    f is proper on spt T and
    g is proper on the full image
    f(spt T), supporting Federer 4.1.7,
    p. 359, under the original single
    hypothesis on their composite. *)
Theorem current_composite_support_properness:
  @is_current_proper_on_support R h2 v n m U hU V T f hFImage /\
  is_proper_map (fun y:set_type (fS @` setT)=>gV (set_val y)).
Proof.
have hF:continuous fS.
  exact:(@current_support_map_continuous R h2 v n m U hU V T f hFImage
    (norm_class_continuous (hf 0%N))).
have hG:=@current_map_on_domain_continuous R n q V W g hGImage
  (norm_class_continuous (hg 0%N)).
have hEqual:gV \o fS=@current_map_on_support R h2 v q m U hU W T (fun x=>g (f x)) hGFImage.
  apply:funext=>x;apply:val_inj;by [].
have hComposite:is_proper_map (gV \o fS) by rewrite hEqual;exact:hpGF.
have hHausdorff:hausdorff_space VT.
  exact:(@set_type_hausdorff YT V (@metric_hausdorff R YT)).
split.
- exact:(@proper_composite_first ST VT WT fS gV hHausdorff hF hG hComposite).
- exact:(@proper_composite_on_image ST VT WT fS gV hF hComposite).
Qed.
Local Notation hpF := current_composite_support_properness.1.
Local Notation hpImage := current_composite_support_properness.2.
Local Notation S := (@CurrentPushforward.value R h2 v n m U V hU hV T f hFImage hf hpF).

(** Source for [current_composite_pushed_support_proper]:
    g is proper on spt(f#T), supporting
    the right side of the original
    composition identity in Federer 4.1.7,
    p. 359. The proved image inclusion
    and actual relative closedness of spt(f#T)
    supply this restriction. *)
Theorem current_composite_pushed_support_proper:
  @is_current_proper_on_support R h2 n q m V hV W S g hGImage.
Proof.
pose A:set VT:=[set y|@current_support R h2 n V hV m S (set_val y)].
pose B:set VT:=fS @` setT.
have [C [hC hSupport]]:=@functional_support_relative_closed R Y (A_m Y R^o m) NY hNY V
  (@current_test_space R h2 n V hV m) (@current_test_value R h2 n V hV m)
  (@current_value R h2 n V hV m S).
have hActual:@current_support R h2 n V hV m S=V `&` C:=hSupport.
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
  have [x hx hFx]:=@current_pushforward_support_image R h2 v n m U V hU hV T f hFImage hf hpF
    (set_val y) hy.
  exists (exist _ x (mem_set hx));first by [].
  apply:val_inj;exact:hFx.
have hNested:=@proper_map_smaller_closed_subset VT WT gV A B hClosed hAB hpImage.
exact:(@current_domain_support_proper_reverse R h2 n q V W g hGImage m hV S hNested).
Qed.
End CurrentCompositeProperness.
