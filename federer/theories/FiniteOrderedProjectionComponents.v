(** Federer (1969), 3.4.8(10), p. 332:
    combine compact finite fibres, prescribed
    local inverses and the original ordering
    to obtain the component homeomorphisms.
    Every topology is the actual subspace topology. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground MetricSubsetBackground HomeomorphismUP EuclideanSubmanifoldUP
  RelativeLocalInverseUP FiniteOrderedEnumeration OrderedFibreSequences FiniteFibreEnumerationCardinality
  FiniteFibreStrataOpen OrderedFibreBranchContinuity ContinuousLocalInverseSheetOpen
  RelativeOpenPartitionComponents ContinuousSectionComponentHomeomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_ordered_projection_components]:
    p_m maps each component of Z
    homeomorphically onto a component of
    Y outside delta=0, 3.4.8(10),
    p. 332. The proof supplies
    the open cardinality strata, continuous ordered
    sections and disjoint relatively open sheets.
    Component correspondence is a conclusion. *)
Theorem finite_ordered_projection_components (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V:set Y) (xi:X->R) (x0:X):
  continuous P ->continuous (fun x:X=>(xi x:real_line_metric R)) ->open V ->
  (forall x,Z x ->V (P x)) ->
  (forall y,V y ->finite_set [set x|Z x /\P x = y]) ->
  (forall x z,Z x ->Z z ->P x = P z ->xi x=xi z ->x=z) ->
  (forall y,V y ->exists C:set Y,nbhs y C /\compact [set x|Z x /\C (P x)]) ->
  (forall x,Z x ->exists U W psi,is_relative_local_inverse P Z x U W psi) ->
  forall x,Z x ->exists F:metric_subset (connected_component Z x)->
      metric_subset (connected_component V (P x)),
    (forall a,val (F a) = P (val a)) /\is_homeomorphism F.
Proof.
move=>hP hXi hV hRange hFinite hInjective hCompact hCharts.
have [S hS]:=@ordered_fibre_sequences_exist R [the choiceType of (X:Type)] Y
  P Z V xi hFinite hInjective.
pose N:=fun y:Y=>#|` fset_set [set x|Z x /\P x = y]|.
pose B:=fun nu:nat=>[set y|V y /\N y=nu].
pose phi:=fun j:nat=>fun y:Y=>nth x0 (S y) j.
have hSize y (hy:V y):N y = size (S y).
  have hEnumeration:=@ordered_sequence_fibre_enumeration R [the choiceType of (X:Type)] Y
    P Z y xi x0 (S y) (hS y hy).
  have h:=(@finite_fibre_enumeration_cardinality [the finType of 'I_(size (S y))]
    [the choiceType of (X:Type)] Y P Z y (fun i=>nth x0 (S y) (i:nat)) hEnumeration).2.
  by rewrite card_ord in h.
have hBOpen nu:open (B nu):=@finite_fibre_strata_open R X Y P Z V xi S x0 hP hV hS hCompact hCharts nu.
have hPoint j y:(j<size (S y))%N ->V y ->Z (phi j y) /\P (phi j y) = y.
  move=>hJ hy;exact:((hS y hy).1 (phi j y)).1 (mem_nth x0 hJ).
have hBranchContinuous nu j:(j<nu)%N ->forall y,B nu y ->{for y,continuous (phi j)}.
  move=>hJ y [hy hN].
  have [C [hC hK]]:=hCompact y hy.
  have hNear:nbhs y V by have h:=hV;rewrite openE in h;exact:h y hy.
  have hIndex:(j<size (S y))%N by rewrite -(hSize y hy) hN.
  exact:(@ordered_fibre_branch_continuous_at R X Y P Z V C xi S x0 y j
    hP hXi hy hNear hC hK hS hCharts hIndex).
have hBranchPoint nu j:(j<nu)%N ->forall y,B nu y ->Z (phi j y) /\P (phi j y) = y.
  move=>hJ y [hy hN];apply:hPoint=>//;by rewrite -(hSize y hy) hN.
pose H:=fun q:(nat*nat)%type=>if (q.2<q.1)%N then phi q.2 @` B q.1 else set0.
have hRelative (q:(nat*nat)%type):relatively_open_set Z (H q).
  case hActive:(q.2<q.1)%N.
  - rewrite /H hActive.
    exact:(@continuous_local_inverse_sheet_open X Y P Z (B q.1) (phi q.2) hP (hBOpen q.1)
      (hBranchContinuous q.1 q.2 hActive) (hBranchPoint q.1 q.2 hActive) hCharts).
  - rewrite /H hActive;exists set0;split;first exact:open0.
    by rewrite setI0.
have hCover x:Z x ->exists q:(nat*nat)%type,H q x.
  move=>hx;have hy:=hRange x hx.
  have hIn:x \in S (P x):=((hS (P x) hy).1 x).2 (conj hx (erefl _)).
  pose j:=index x (S (P x)).
  have hJ:(j<N (P x))%N by rewrite hSize // /j index_mem.
  exists (N (P x),j);rewrite /H /= hJ.
  exists (P x);first by split.
  exact:nth_index hIn.
have hDisjoint (q r:(nat*nat)%type):q!=r ->forall x,H q x ->~H r x.
  case:q=>nu j;case:r=>mu i=>hDifferent x.
  rewrite /H /=.
  case hJ:(j<nu)%N;last by [].
  case hI:(i<mu)%N;last by move=>_ hFalse;exact:hFalse.
  move=>[y hy hY] [z hz hZ].
  have hPy:P x = y by rewrite -hY;exact:(hBranchPoint nu j hJ y hy).2.
  have hPz:P x = z by rewrite -hZ;exact:(hBranchPoint mu i hI z hz).2.
  have hYZ:y=z by rewrite -hPy -hPz.
  have hNu:nu=mu by rewrite -hy.2 -hz.2 hYZ.
  have hJSize:(j<size (S y))%N by rewrite -(hSize y hy.1) hy.2.
  have hISize:(i<size (S y))%N by rewrite -(hSize y hy.1) hy.2 hNu.
  have hEqual:phi j y = phi i y by rewrite hY hYZ hZ.
  have hTrans:transitive (fun x z:X=>xi x<xi z) by move=>u v w;exact:lt_trans.
  have hIrr:irreflexive (fun x z:X=>xi x<xi z) by move=>u;exact:ltxx.
  have hUniq:uniq (S y):=@sorted_uniq X (fun u v=>xi u<xi v) hTrans hIrr (S y) (hS y hy.1).2.
  have hJI:j = i.
    apply/eqP;rewrite -(@nth_uniq X x0 (S y) j i hJSize hISize hUniq);apply/eqP;exact:hEqual.
  by rewrite hNu hJI eqxx in hDifferent.
have hBaseRelative nu:relatively_open_set V (B nu).
  exists (B nu);split;first exact:hBOpen nu.
  apply/seteqP;split=>y.
  - move=>hy;by split;[exact:hy.1|exact:hy].
  - by move=>[_ hy].
have hBaseCover y:V y ->exists nu,B nu y by move=>hy;exists (N y);by split.
have hBaseDisjoint nu mu:nu!=mu ->forall y,B nu y ->~B mu y.
  move=>hDifferent y hy hz.
  have hEqual:nu=mu by rewrite -hy.2 -hz.2.
  by rewrite hEqual eqxx in hDifferent.
move=>x hx.
have [q hQ]:=hCover x hx.
case hActive:(q.2<q.1)%N;last by move:hQ;rewrite /H hActive.
have [y hy hY]:(phi q.2 @` B q.1) x by move:hQ;rewrite /H hActive.
have hPx:P x = y by rewrite -hY;exact:(hBranchPoint q.1 q.2 hActive y hy).2.
have hXComponent:=@relative_open_partition_components X [the eqType of ((nat*nat)%type:Type)]
  Z H hRelative hCover hDisjoint q x hQ.
rewrite /H hActive -hY in hXComponent.
have hYComponent:=@relative_open_partition_components Y [the eqType of (nat:Type)]
  V B hBaseRelative hBaseCover hBaseDisjoint q.1 y hy.
have hHomeomorphism:=@continuous_section_component_homeomorphism R X Y P (B q.1) (phi q.2) y
  hP (hBranchContinuous q.1 q.2 hActive) (fun z hz=>(hBranchPoint q.1 q.2 hActive z hz).2) hy.
rewrite -hXComponent -hYComponent hY -hPx in hHomeomorphism.
exact:hHomeomorphism.
Qed.
