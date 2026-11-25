(** Federer (1969), 4.1.7, p. 359:
    the original proper pushforward preserves
    local normality and normality. Representability
    follows from the exact scalar gauge bound;
    boundary commutation and the support-image law
    give the two remaining defining conditions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion CurrentBoundary CurrentBoundarySupport CurrentProperSupport
  CurrentPushforwardSealed CurrentPushforwardVariation CurrentPushforwardBoundary CurrentPushforwardSupport
  CurrentSupportGeometry CurrentSupportMapTopology NormalCurrentsUP SmoothCompactSet IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardNormality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.

(** Source for [current_pushforward_locally_normal]:
    f# maps N_m^loc(U) into N_m^loc(V),
    Federer 4.1.7, p. 359. Properness
    for the boundary is derived from
    its smaller original support. The
    degree-zero boundary convention is retained. *)
Theorem current_pushforward_locally_normal m (T:@current_space R h2 v U hU m)
    (hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage):
  @is_locally_normal_current R h2 v U hU m T->
  @is_locally_normal_current R h2 n V hV m
    (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Proof.
move=>hN;split.
- exact:(@current_pushforward_representable R h2 v n m U V hU hV T hN.1 f hImage hf hp).
- case:m T hp hN=>[|p] T hp hN;first by [].
  pose bd:=@current_boundary R h2 v p U hU T.
  pose hPB:=@current_pushforward_boundary_proper R h2 v n p U V hU T f hImage hp.
  change (@is_integration_representable_current R h2 n p V hV
    (@current_boundary R h2 n p V hV
      (@CurrentPushforward.value R h2 v n p.+1 U V hU hV T f hImage hf hp))).
  rewrite (@current_pushforward_boundary R h2 v n p U V hU hV T f hImage hf hp).
  exact:(@current_pushforward_representable R h2 v n p U V hU hV bd hN.2 f hImage hf hPB).
Qed.

(** Source for [current_pushforward_compact_support]:
    the support-image law preserves compact
    support under the original smooth map,
    supporting normality in Federer 4.1.7,
    p. 359. The map is required
    to be defined and smooth only on U. *)
Theorem current_pushforward_compact_support m (T:@current_space R h2 v U hU m)
    (hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage):
  @compact XT (@current_support R h2 v U hU m T)->
  @compact YT (@current_support R h2 n V hV m
    (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp)).
Proof.
move=>hCompact.
pose support:=@current_support R h2 v U hU m T.
pose ST:topologicalType:=[the topologicalType of set_type (support:set XT)].
pose VT:=current_domain R n V.
pose mapS:=@current_map_on_support R h2 v n m U hU V T f hImage.
have hWhole:@compact ST setT.
  have hPre:=@set_type_compact_preimage XT support support hCompact (fun x hx=>hx).
  have hEqual:(set_val @^-1` support:set ST)=setT.
    apply/seteqP;split;first by [].
    move=>x _;exact:set_valP x.
  by rewrite hEqual in hPre.
have hMap:continuous mapS.
  exact:(@current_support_map_continuous R h2 v n m U hU V T f hImage
    (norm_class_continuous (hf 0%N))).
have hAmbient:continuous (fun x:ST=>(f (set_val x):YT)).
  move=>x;exact:(continuous_comp (hMap x) (@set_type_val_continuous YT V (mapS x))).
have hImageCompact:@compact YT (f @` support).
  have hC:=continuous_compact (continuous_subspaceT hAmbient) hWhole.
  have hEqual:(fun x:ST=>(f (set_val x):YT)) @` setT=f @` support.
    apply/seteqP;split.
    + move=>y [x _ <-];exists (set_val x);first exact:set_valP x.
      by [].
    + move=>y [x hx <-];exists (exist _ x (mem_set hx));by [].
  by rewrite hEqual in hC.
have hInDomain:f @` support `<=` V.
  move=>y [x hx <-];exact:hImage x hx.1.
pose K:=@Build_smooth_compact_set R Y NY hNY V (f @` support) hInDomain hImageCompact.
exact:(@current_support_compact_bound R h2 n m V hV K
  (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp)
  (@current_pushforward_support_image R h2 v n m U V hU hV T f hImage hf hp)).
Qed.

(** Source for [current_pushforward_normal]:
    f# maps the original normal currents
    into normal currents, Federer 4.1.7,
    p. 359. This uses their original
    local-normality and compact-support definition. *)
Theorem current_pushforward_normal m (T:@current_space R h2 v U hU m)
    (hp:@is_current_proper_on_support R h2 v n m U hU V T f hImage):
  @is_normal_current R h2 v U hU m T->
  @is_normal_current R h2 n V hV m
    (@CurrentPushforward.value R h2 v n m U V hU hV T f hImage hf hp).
Proof.
move=>hN;split.
- exact:(current_pushforward_locally_normal hp hN.1).
- exact (@current_pushforward_compact_support m T hp hN.2).
Qed.
End CurrentPushforwardNormality.
