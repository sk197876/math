(** Federer (1969), 4.1.7, p. 359:
    properness is required only on the
    original current support. This supporting
    measure theorem adapts the proved closed-map
    argument of 2.2.17, p. 72, to
    a Radon measure carried by that locus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import MeasureUP MeasureBasic MeasureNullModification MeasurePushforward RadonMeasureUP
  ProperMapUP ProperContinuousClosed PushforwardMeasurableSets IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section RadonCarriedProperPushforward.
Variable R:realType.
Variables X Y:topologicalType.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable S:set X.
Hypothesis hCarried:mu (~` S)=0.
Variable f:X->Y.
Hypothesis hf:continuous f.
Local Notation ST := [the topologicalType of set_type S].
Local Notation fS := (fun x:ST=>f (set_val x)).

(** Source for [carried_measure_intersection_value]:
    intersecting with the original carrying locus
    preserves every outer mass, supporting Federer
    4.1.7, p. 359. This is the
    numerical null-invariance already proved from
    2.1.2, pp. 53–54. *)
Lemma carried_measure_intersection_value A:mu A=mu (S `&` A).
Proof.
apply:(@measure_null_modification_value R X mu hm A (S `&` A) (~` S) hCarried)=>x hNot.
have hS:S x by apply:contrapT=>h;exact:hNot h.
split;[by move=>hA;split|by move=>[_ hA]].
Qed.

(** Source for [carried_proper_compact_preimage]:
    the original carrying locus intersected with
    an inverse compact image is compact,
    supporting Federer 4.1.7, p. 359.
    Properness away from the locus is unused. *)
Lemma carried_proper_compact_preimage:
  is_proper_map fS->forall K:set Y,compact K->compact (S `&` (f @^-1` K)).
Proof.
move=>hp K hK.
have hPre:=hp K hK.
have hCompact:compact (set_val @` (fS @^-1` K)).
  apply:continuous_compact hPre;apply:continuous_subspaceT=>x;exact:set_type_val_continuous.
have hEqual:set_val @` (fS @^-1` K)=S `&` (f @^-1` K).
  apply/seteqP;split.
  - move=>x [z hz <-];exact:conj (set_valP z) hz.
  - move=>x [hx hFx];exists (exist _ x (mem_set hx));by [].
by rewrite hEqual in hCompact.
Qed.

(** Source for [carried_proper_radon_pushforward]:
    the image of a Radon measure carried
    by S is Radon when f restricted
    to S is proper, supporting the original
    support-proper weighted variation in Federer
    4.1.7, p. 359. No separate
    properness of f on all X is assumed. *)
Theorem carried_proper_radon_pushforward:
  hausdorff_space Y->locally_compact (@setT Y)->is_proper_map fS->
  is_radon_measure (measure_pushforward f mu).
Proof.
move=>hY hLocal hp.
have hFS:continuous (fS:ST->Y).
  move=>x.
  exact (@continuous_comp ST X Y (fun a:ST=>(set_val a:X)) f x
    (@set_type_val_continuous X S x) (@hf (set_val x))).
have hClosed:=@proper_continuous_map_closed ST Y fS hY hLocal hFS hp.
have hPreOpen A:open A->open (f @^-1` A):=((@continuousP X Y f).1 hf) A.
constructor=>//.
- move=>K hK.
  change (mu (f @^-1` K) < +oo).
  rewrite (carried_measure_intersection_value (f @^-1` K)).
  exact:(radon_compact_finite hr (carried_proper_compact_preimage hp hK)).
- move=>A hA;apply:pushforward_measurable_from_preimage.
  exact:(@radon_open_measurable R X mu hr (f @^-1` A) (@hPreOpen A hA)).
- move=>A hA c hc;apply:(@radon_inner_least R X mu hr (f @^-1` A) (@hPreOpen A hA) c).
  move=>K hK hKA.
  have hImage:compact (f @` K).
    apply:continuous_compact hK;exact:continuous_subspaceT hf.
  have hIn:f @` K `<=` A by move=>y [x hx <-];exact:hKA x hx.
  apply:le_trans _ (hc (f @` K) hImage hIn).
  apply:(@measure_mono R X mu hm K (f @^-1` (f @` K)))=>x hx;by exists x.
- move=>B c hc;apply:(@radon_outer_greatest R X mu hr (f @^-1` B) c)=>O hO hBO.
  pose C:set ST:=set_val @^-1` (~` O).
  have hC:closed C.
    apply:(@preimage_closed ST X (fun x:ST=>(set_val x:X)) (~` O)
      _ (open_closedC hO)).
    by move=>x _;exact:(@set_type_val_continuous X S x).
  pose W:=~` (fS @` C).
  have hW:open W:=closed_openC (hClosed C hC).
  have hBW:B `<=` W.
    move=>y hy [x hx hFx];apply:hx;apply:hBO;change (B (f (set_val x)));by rewrite hFx.
  apply:le_trans (hc W hW hBW) _.
  change (mu (f @^-1` W)<=mu O).
  rewrite (carried_measure_intersection_value (f @^-1` W)).
  apply:(@measure_mono R X mu hm (S `&` (f @^-1` W)) O)=>x [hx hWx].
  apply:contrapT=>hOff;apply:hWx.
  exists (exist _ x (mem_set hx));by [].
Qed.
End RadonCarriedProperPushforward.
