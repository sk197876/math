(** Federer (1969), 3.2.39, p. 275: expand the
    cited 2.10.8 into finite disjoint original Borel pieces. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology lra.
From Federer Require Import BorelCoverCostUP BorelCaratheodoryMeasure BorelPartition BorelPartitionCoverBounds
  BorelPartitionCharacterization NonnegativeSum ExtendedRealBoundsUP MeasureUP MeasureBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_partition_cost_approximation]:
    supporting the 2.10.8 appeal in Federer 3.2.39,
    p. 275. The complete Borel-partition supremum and the
    independent finite-subsum law give finitely many disjoint
    original Borel pieces whose cost sum nearly attains the
    finite measure. Their union need not be the whole source.
    The later compact grid provides the exact compact cover. *)
Theorem finite_borel_partition_cost_approximation (R:realType) (X:metricType R)
    (c:set X->\bar R) (A:set X) (e:R):
  is_borel_cover_cost c ->(exists D:set X,countable D /\dense D) ->borel_set A ->
  borel_caratheodory_measure c A< +oo ->(0<e)%R ->
  exists (I:finType) (S:I->set X),
    (forall i,borel_set (S i) /\S i `<=` A) /\
    (forall i j,i!=j ->S i `&` S j=set0) /\
    borel_caratheodory_measure c A<=(\sum_i c (S i))+e%:E.
Proof.
move=>hc [D [hD hDense]] hA hFinite he.
pose nu:=borel_caratheodory_measure c.
pose hn:=borel_caratheodory_is_measure hc.
have hFin:nu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hn A)).
pose q:=fine (nu A).
have hValue:nu A=q%:E by rewrite /q fineK.
have hSup:=@borel_partition_cost_supremum_all R X c hc D A hD hDense hA.
have hStrict:(q-e/2)%R%:E<nu A.
  rewrite hValue lte_fin ltrBlDr ltrDl divr_gt0 //; exact:ltr0n.
have [H [hH hLarge]]:exists H,is_borel_partition A H /\
    (q-e/2)%R%:E<borel_partition_cost c H.
  apply:contrapT=>hNo.
  have hUpper:nu A<=(q-e/2)%R%:E.
    apply:(extended_real_supremum_least hSup)=>z [H [hH ->]].
    rewrite leNgt; apply/negP=>hz; apply:hNo; exists H; by split.
  by have :=lt_le_trans hStrict hUpper; rewrite ltxx.
have hThreshold:(q-e)%R%:E<borel_partition_cost c H.
  by apply:lt_trans _ hLarge; rewrite lte_fin ltrD2l ltrN2 ltr_pdivrMr ?ltr0n // mulr_natr mulr2n ltrDl.
have [B [hBH hBig]]:exists B:{fset set X},
    (forall S,S \in B ->H S) /\(q-e)%R%:E<(\sum_(S <- B) c S).
  apply:contrapT=>hNo.
  have hBound:borel_partition_cost c H<=(q-e)%R%:E.
    apply:nonnegative_sum_least=>B hB.
    rewrite leNgt; apply/negP=>hBig; apply:hNo; exists B; by split.
  by have :=lt_le_trans hThreshold hBound; rewrite ltxx.
pose I:=[the finType of 'I_(size (B:seq (set X)))].
pose S (i:I):set X:=nth set0 B i.
have hMember i:H (S i).
  apply:(hBH (S i)); exact:mem_nth (ltn_ord i).
have hIndex (i j:I):S i=S j ->i=j.
  move=>hEqual; apply:val_inj; apply/eqP.
  rewrite -(@nth_uniq [the eqType of set X] set0 (B:seq (set X)) i j
    (ltn_ord i) (ltn_ord j) (fset_uniq B)).
  exact/eqP.
have hWithin i:S i `<=` A.
  move=>x hx; rewrite -(borel_partition_union hH); exists (S i)=>//; exact:hMember i.
have hDisjoint i j:i!=j ->S i `&` S j=set0.
  move=>hij; apply:(borel_partition_disjoint hH (hMember i) (hMember j)).
  move=>hEqual; apply:(elimN eqP hij); exact:hIndex hEqual.
have hBorel i:borel_set (S i):=borel_partition_members hH (hMember i).
exists I,S; split; first by move=>i; split; [exact:hBorel i|exact:hWithin i].
split; first exact hDisjoint.
rewrite (big_nth set0) big_mkord in hBig.
rewrite /nu in hValue.
have hBound:((q-e)%R%:E<=(\sum_(i:I) c (S i)))%E:=ltW hBig.
rewrite EFinB in hBound.
have hEFin:e%:E \is a fin_num by rewrite fin_numE.
rewrite (@leeBlDr R q%:E e%:E (\sum_(i:I) c (S i))%E hEFin) in hBound.
rewrite hValue; exact hBound.
Qed.
