(** Federer (1969), 3.2.31, p. 269: supporting compact refinement
    of a finite open cover whose closed enlargements have null
    boundaries. First-hit differences of the closed enlargements
    have only boundary overlaps. All witnesses remain local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import MeasureUP MeasureAlmostBasic FiniteCompactNullOverlapCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_compact_null_overlap_cover_exists]: supporting
    the finite sum of locally rescaled estimates in Federer 3.2.31,
    p. 269. The closed first-hit pieces stay compact and their
    overlaps are subsets of the given null boundaries. Existence
    is proved from elementary topology and the measure laws. *)
Theorem finite_compact_null_overlap_cover_exists (R:realType) (X:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (K:set X) N (U C:nat->set X):
  compact K ->
  (forall i,(i<N)%N ->open (U i)) ->
  (forall i,(i<N)%N ->closed (C i)) ->
  (forall i,(i<N)%N ->U i `<=` C i) ->
  (forall i,(i<N)%N ->mu (C i `\` U i)=0) ->
  K `<=` \bigcup_(i in [set i|(i<N)%N]) U i ->
  exists D,is_finite_compact_null_overlap_cover mu K N C D.
Proof.
move=>hK hU hC hUC hBoundary hCover.
pose D i:=(K `&` C i) `\` \bigcup_(j in [set j|(j<i)%N]) U j.
have hDsub i:D i `<=` K `&` C i by move=>x [hx _].
have hDcompact i (hi:(i<N)%N):compact (D i).
  apply:compact_closedI (compact_closedI hK (hC i hi)) _.
  apply:open_closedC; apply:bigcup_open=>j hj.
  exact (hU j (ltn_trans hj hi)).
have hUnion:(\bigcup_(i in [set i|(i<N)%N]) D i)=K.
  apply/seteqP; split=>x.
  - move=>[i hi hx]; exact (hDsub i x hx).1.
  - move=>hx; have [j hj hxj]:=hCover x hx.
    pose P i:=`[< (i<N)%N /\ U i x >].
    have hP:exists i,P i by exists j; apply/asboolP; by split.
    have [i /asboolP [hi hxi] hMin]:=ex_minnP hP.
    exists i=>//; split; first by split=>//; exact (hUC i hi x hxi).
    move=>[k hk hxk].
    have hkN:(k<N)%N:=ltn_trans hk hi.
    have hkP:P k by apply/asboolP; by split.
    have hLe:=hMin k hkP.
    have hklt:(k<i)%N:=hk.
    by move:hklt; rewrite ltnNge hLe.
have hPair i j (hi:(i<N)%N) (hj:(j<N)%N) (hne:i!=j):mu (D i `&` D j)=0.
  case: (ltngtP i j)=>hij.
  - apply:(@measure_null_subset R X mu hm _ (C i `\` U i))=>//; last exact (hBoundary i hi).
    move=>x [hxi hxj]; split; first exact (hDsub i x hxi).2.
    move=>hxU; apply:hxj.2; exists i=>//.
  - apply:(@measure_null_subset R X mu hm _ (C j `\` U j))=>//; last exact (hBoundary j hj).
    move=>x [hxi hxj]; split; first exact (hDsub j x hxj).2.
    move=>hxU; apply:hxi.2; exists j=>//.
  - by move: hne; rewrite hij eqxx.
exists D; constructor=>//.
Qed.
