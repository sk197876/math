(** Federer (1969), 4.1.7, p. 359:
    a continuous map proper on
    the original current support has
    relatively closed support image. The
    supporting closed-map theorem is the
    one already proved for 2.2.17,
    p. 72. The target remains
    the original open Euclidean domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormClassOneUP NormClassZeroTopology InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces CurrentDomain CurrentDomainGeometry CurrentProperSupport
  IsotropyGroupTopology SubtypeCompactHausdorff ProperContinuousClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_open_image]:
    an open subset of the
    original open domain is ambient
    open, supporting the complement-of-image
    argument in Federer 4.1.7,
    p. 359, by the relative
    topology of 2.2.17, p. 72. *)
Lemma open_subspace_open_image (X:topologicalType) (U:set X) (A:set (set_type U)):
  open U->open A->open (set_val @` A).
Proof.
move=>hU [W hW <-].
have hEqual:set_val @` (set_val @^-1` W:set (set_type U))=U `&` W.
  apply/seteqP;split.
  - move=>x [y hy <-];exact:conj (set_valP y) hy.
  - move=>x [hx hWx];exists (exist _ x (mem_set hx));by [].
rewrite hEqual;exact:openI hU hW.
Qed.

Section CurrentSupportMapTopology.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable V:set Y.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable T:@current_space R h2 v U hU m.
Local Notation support := (@current_support R h2 v U hU m T).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation UT := (current_domain R v U).
Local Notation VT := (current_domain R n V).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hF:norm_class_zero NX NY U f.
Local Notation mapS := (@current_map_on_support R h2 v n m U hU V T f hImage).

(** Source for [current_support_map_continuous]:
    the actual restriction f|spt T
    is continuous into the original
    domain V, supporting Federer 4.1.7,
    p. 359. No extension of
    f outside U is required. *)
Theorem current_support_map_continuous:continuous mapS.
Proof.
pose j:ST->UT:=fun x=>exist _ (set_val x) (mem_set (set_valP x).1).
have hJ:continuous j.
  apply:(@set_type_continuous_into XT U ST j).
  exact:(@set_type_val_continuous XT support).
have hOriginal:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U f hF.
apply:(@set_type_continuous_into YT V ST mapS).
move=>x;exact:(@continuous_comp ST [the topologicalType of UT]
  [the topologicalType of YT] j (fun y:UT=>(f (set_val y):YT)) x
  (hJ x) (hOriginal (j x))).
Qed.

(** Source for [current_proper_support_image_complement_open]:
    V minus f(spt T) is
    open in the ambient target,
    supporting the original support-image inclusion
    in Federer 4.1.7, p. 359.
    Only properness on spt T
    and the printed domain hypotheses
    enter the argument. *)
Theorem current_proper_support_image_complement_open:
  @is_current_proper_on_support R h2 v n m U hU V T f hImage->
  @open YT [set y|V y /\~exists x,support x /\f x=y].
Proof.
move=>hProper.
have hHausdorff:hausdorff_space VT.
  exact:(@set_type_hausdorff YT V (@metric_hausdorff R YT)).
have hClosed:=@proper_continuous_map_closed ST VT mapS hHausdorff
  (@current_domain_locally_compact R n V hV) current_support_map_continuous hProper setT closedT.
have hOpenV:@open YT V.
  rewrite openE=>y hy;exact:(@norm_domain_interior_neighbourhood R Y NY hNY V y).1 (hV y hy).
have hOpen:=@open_subspace_open_image YT V (~` (mapS @` setT)) hOpenV (closed_openC hClosed).
have hEqual:set_val @` (~` (mapS @` setT))=[set y|V y /\~exists x,support x /\f x=y].
  apply/seteqP;split.
  - move=>y [z hz <-];split;first exact:set_valP z.
    move=>[x [hx hFx]];apply:hz.
    exists (exist _ x (mem_set hx));first by [].
    apply:val_inj;exact:hFx.
  - move=>y [hy hNo];exists (exist _ y (mem_set hy));last by [].
    move=>[x _ hFx];apply:hNo;exists (set_val x);split;first exact:set_valP x.
    exact:(congr1 set_val hFx).
by rewrite hEqual in hOpen.
Qed.
End CurrentSupportMapTopology.
