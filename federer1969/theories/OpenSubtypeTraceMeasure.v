(** General topology and measure theory supporting Federer (1969),
    4.1.13, pp. 369–370: retain the original variation measure when
    replacing the source by an open neighbourhood of the support.
    The trace is the existing image-pullback measure of 2.1.2,
    pp. 53–54. Its Radon laws follow from 2.2.5, pp. 62–63,
    and the actual topologies of the two open subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward
  MeasureRestriction MeasureNullModification MeasureImagePullback
  RadonMeasureUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section OpenSubtypeInclusion.
Variable X:topologicalType.
Variables U V:set X.
Hypothesis hUV:forall x,U x->V x.
Local Notation UT := [the topologicalType of set_type U].
Local Notation VT := [the topologicalType of set_type V].

(** Source for [open_subtype_inclusion]: the identity inclusion of
    the smaller source in Federer 4.1.13, pp. 369–370, on its actual
    point types. This transparent abbreviation changes only the
    membership proof, not the original point. *)
Definition open_subtype_inclusion (x:UT):VT:=
  exist _ (set_val x) (mem_set (@hUV _ (set_valP x))).
Local Notation inc := open_subtype_inclusion.

(** Source for [open_subtype_inclusion_value]: the source inclusion
    leaves each original point unchanged, supporting the source
    replacement in Federer 4.1.13, pp. 369–370. *)
Lemma open_subtype_inclusion_value x:set_val (inc x)=set_val x.
Proof. by []. Qed.

(** Source for [open_subtype_inclusion_injective]: the original
    source inclusion is injective, as required by the exact image
    integral of 2.4.18, p. 90, in 4.1.13, pp. 369–370. *)
Lemma open_subtype_inclusion_injective:injective inc.
Proof.
move=>x y h;apply:val_inj;exact:(congr1 set_val h).
Qed.

(** Source for [open_subtype_inclusion_continuous]: the identity
    inclusion is continuous for the original subspace topologies;
    general topology supporting Federer 4.1.13, pp. 369–370. *)
Lemma open_subtype_inclusion_continuous:continuous inc.
Proof.
apply:(@set_type_continuous_into X V UT inc).
exact:(@set_type_val_continuous X U).
Qed.

(** Source for [open_subtype_inclusion_open_image]: an open subset
    of the smaller open source is open in the larger source;
    general topology supporting Federer 4.1.13, pp. 369–370. *)
Lemma open_subtype_inclusion_open_image:
  open U->forall O:set UT,open O->open (inc @` O).
Proof.
move=>hU O [B hB <-].
have hSet:inc @` (set_val @^-1` B)=
    (set_val @^-1` (U `&` B):set VT).
  apply/seteqP;split.
  - move=>y [x hx <-];exact:conj (set_valP x) hx.
  - move=>y [hyU hyB].
    exists (exist _ (set_val y) (mem_set hyU));first exact:hyB.
    apply:val_inj;by [].
rewrite hSet.
exact:((@continuousP VT X set_val).1
  (@set_type_val_continuous X V) _ (openI hU hB)).
Qed.

(** Source for [open_subtype_inclusion_compact_preimage]: a compact
    subset of the larger source contained in the inclusion image is
    compact in the smaller source. This is general topology used
    with the Radon compact laws of 2.2.5, pp. 62–63, in Federer
    4.1.13, pp. 369–370. No properness on the whole source is assumed. *)
Lemma open_subtype_inclusion_compact_preimage (K:set VT):
  compact K->K `<=` inc @` setT->compact (inc @^-1` K).
Proof.
move=>hK hRange.
pose C:set X:=set_val @` K.
have hC:compact C.
  apply:continuous_compact hK.
  exact:continuous_subspaceT (@set_type_val_continuous X V).
have hCU:C `<=` U.
  move=>x [y hy <-].
  have[z _ hzy]:=hRange y hy.
  by rewrite -hzy;exact:(set_valP z).
have hEqual:(inc @^-1` K)=(set_val @^-1` C:set UT).
  apply/seteqP;split.
  - move=>x hx;exists (inc x);by [].
  - move=>x [y hy hxy].
    have hSame:y=inc x by apply:val_inj;exact:hxy.
    change (K (inc x));by rewrite -hSame.
rewrite hEqual.
exact:(@set_type_compact_preimage X U C hC hCU).
Qed.
End OpenSubtypeInclusion.

Section OpenSubtypeTraceMeasure.
Variable R:realType.
Variable X:topologicalType.
Variables U V:set X.
Hypothesis hUV:forall x,U x->V x.
Local Notation UT := [the topologicalType of set_type U].
Local Notation VT := [the topologicalType of set_type V].
Local Notation inc := (@open_subtype_inclusion X U V hUV).
Variable mu:set VT->\bar R.

(** Source for [open_subtype_trace_measure]: the original measure
    evaluated on the image of a set in the smaller source, by
    2.1.2, p. 54; supporting the variation integrals in Federer
    4.1.13, pp. 369–370. Use the existing image-pullback operation. *)
Definition open_subtype_trace_measure:set UT->\bar R:=
  measure_image_pullback inc mu.
Local Notation tau := open_subtype_trace_measure.

(** Source for [open_subtype_trace_is_measure]: the original trace
    satisfies the measure laws of 2.1.2, pp. 53–54; supporting
    Federer 4.1.13, pp. 369–370. *)
Lemma open_subtype_trace_is_measure:
  is_measure mu->is_measure tau.
Proof. exact:measure_image_pullback_is_measure. Qed.

(** Source for [open_subtype_trace_radon]: the original Radon
    measure remains Radon on the smaller open source, by the
    compact, open and outer regularity laws of 2.2.5, pp. 62–63;
    supporting Federer 4.1.13, pp. 369–370. Empty subspaces are allowed. *)
Theorem open_subtype_trace_radon:
  is_measure mu->is_radon_measure mu->open U->
  hausdorff_space UT->locally_compact (@setT UT)->is_radon_measure tau.
Proof.
move=>hm hr hU hHaus hLocal.
have hInj:=@open_subtype_inclusion_injective X U V hUV.
have hCont:=@open_subtype_inclusion_continuous X U V hUV.
have hOpen:=@open_subtype_inclusion_open_image X U V hUV hU.
constructor=>//.
- move=>K hK;apply:(radon_compact_finite hr).
  apply:continuous_compact hK;exact:continuous_subspaceT hCont.
- move=>O hO.
  exact:(@measure_image_pullback_measurable R UT VT inc mu O hInj
    (@radon_open_measurable R VT mu hr (inc @` O) (hOpen O hO))).
- move=>O hO c hc.
  apply:(@radon_inner_least R VT mu hr (inc @` O) (hOpen O hO) c).
  move=>K hK hKO.
  have hRange:K `<=` inc @` setT.
    move=>y hy;have[x hx hxy]:=hKO y hy;exists x;by [].
  have hCompact:=@open_subtype_inclusion_compact_preimage X U V hUV K hK hRange.
  have hSubset:inc @^-1` K `<=` O.
    move=>x hx;have[y hy hyx]:=hKO (inc x) hx.
    have hSame:y=x:=hInj y x hyx.
    by rewrite -hSame.
  have hEqual:inc @` (inc @^-1` K)=K.
    apply/seteqP;split.
    * by move=>y [x hx <-].
    * move=>y hy;have[x _ hxy]:=hRange y hy.
      exists x;last exact:hxy.
      change (K (inc x));by rewrite hxy.
  have hBound:=hc _ hCompact hSubset.
  change (is_true (mu (inc @` (inc @^-1` K))<=c)) in hBound.
  by rewrite hEqual in hBound.
- move=>A c hc;apply:(@radon_outer_greatest R VT mu hr (inc @` A) c).
  move=>O hO hAO.
  have hPre:open (inc @^-1` O):=((@continuousP UT VT inc).1 hCont) O hO.
  have hSubset:A `<=` inc @^-1` O.
    move=>x hx;apply:hAO;by exists x.
  apply:le_trans (hc _ hPre hSubset) _.
  apply:(@measure_mono R VT mu hm)=>y [x hx <-];exact:hx.
Qed.

(** Source for [open_subtype_trace_pushforward]: the inclusion
    image of the original trace is the restriction to the smaller
    source, by 2.1.2, p. 54; supporting the exact integral transport
    of Federer 4.1.13, pp. 369–370. Every target set is retained. *)
Lemma open_subtype_trace_pushforward:
  measure_pushforward inc tau=
    measure_restrict mu [set x:VT|U (set_val x)].
Proof.
apply:funext=>A;rewrite /measure_pushforward /open_subtype_trace_measure
  /measure_image_pullback /measure_restrict.
congr mu;apply/seteqP;split.
- move=>y [x hx <-];exact:conj (set_valP x) hx.
- move=>y [hyU hyA].
  pose x:UT:=exist _ (set_val y) (mem_set hyU).
  have hSame:inc x=y by apply:val_inj;by [].
  exists x;last exact:hSame.
  change (A (inc x));by rewrite hSame.
Qed.

(** Source for [open_subtype_carried_trace_pushforward]: if the
    original measure is carried by the smaller source, inclusion
    recovers it on every set, by null invariance in 2.1.2,
    pp. 53–54; supporting Federer 4.1.13, pp. 369–370. *)
Lemma open_subtype_carried_trace_pushforward:
  is_measure mu->mu [set x:VT|~U (set_val x)]=0->
  measure_pushforward inc tau=mu.
Proof.
move=>hm hCarried;rewrite open_subtype_trace_pushforward.
apply:funext=>A;rewrite /measure_restrict.
apply:(@measure_null_modification_value R VT mu hm
  ([set x:VT|U (set_val x)] `&` A) A
  [set x:VT|~U (set_val x)] hCarried).
move=>x hx.
have hUx:U (set_val x) by apply:contrapT=>h;exact:hx h.
by split;[move=>[_ hA]|move=>hA;split].
Qed.
End OpenSubtypeTraceMeasure.
