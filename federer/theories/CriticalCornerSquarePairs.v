(** Federer (1969), 3.3.20, pp. 308–309:
    actual distinct original opposite-corner square pairs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EuclideanInnerProduct
  InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP CriticalCornerCoordinate
  CriticalCornerIntervalSelection CriticalCornerPairingPatternsUP CriticalCornerPatternIndices
  CriticalCornerCoordinateSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_corner_actual_square_pairs]:
    the finite corner-offset patterns yield pairwise
    distinct ACTUAL original G_j squares, with the
    original opposite-corner distance, in 3.3.20,
    pp. 308–309. Original interval membership,
    endpoint uniqueness and actual Euclidean coordinate
    gaps discharge every part of the certificate.
    The auxiliary selection and pairing remain local. *)
Theorem critical_corner_actual_square_pairs (R:realType) (r:R)
    (F:{fset compact_real_intervals R})
    (G:{fset (compact_real_intervals R*compact_real_intervals R)})
    C n budget L:
  0<r ->G=(F `*` F)%fset ->
  is_critical_corner_interval_selection r F C ->
  is_critical_corner_pairing_pattern n budget L ->
  (forall p,p \in L ->((p.1+1)%:R:R)/r<=1/4 /\((p.2+1)%:R:R)/r<=1/4) ->
  exists e:((bool*'I_(size L))*bool)->(compact_real_intervals R*compact_real_intervals R),
    injective e /\(forall i,e i \in G) /\
    forall i p q,euclidean_interval_rectangle (e (i,false)).1 (e (i,false)).2 p ->
      euclidean_interval_rectangle (e (i,true)).1 (e (i,true)).2 q ->
      Num.sqrt 2 * (1-(budget+4)%:R/(2*r))<=mdist p q.
Proof.
move=>hr hG hC hPattern hSize.
pose O (t:bool) (i:'I_(size L)):=nth (0,0) (if t then rev L else L) i.
pose e (k:((bool*'I_(size L))*bool)):=
  (C k.2 (O k.2 k.1.2).1,C (if k.2 then negb k.1.1 else k.1.1) (O k.2 k.1.2).2).
have hMember t i:O t i \in L.
  rewrite /O;case:t=>[|];last exact:mem_nth (ltn_ord i).
  rewrite -mem_rev;apply:mem_nth;by rewrite size_rev;exact:ltn_ord.
have hOffsets t i:(O t i).1 \in [::0;3;12;15] /\(O t i).2 \in [::0;3;12;15].
  exact:(@critical_corner_pattern_index_offsets n budget L hPattern t i).
have hSizes t i:(((O t i).1+1)%:R:R)/r<=1/4 /\(((O t i).2+1)%:R:R)/r<=1/4.
  exact:hSize _ (hMember t i).
have hInjection:injective e.
  move=>[[b i] t] [[d k] s] hEqual.
  have hFirst:=congr1 fst hEqual.
  have hSecond:=congr1 snd hEqual.
  have [hTS hX]:=@critical_corner_interval_selection_injective R r F C hC hr
    t s (O t i).1 (O s k).1 (hOffsets t i).1 (hOffsets s k).1
    (hSizes t i).1 (hSizes s k).1 hFirst.
  subst s.
  have [hBD hY]:=@critical_corner_interval_selection_injective R r F C hC hr
    (if t then negb b else b) (if t then negb d else d)
    (O t i).2 (O t k).2 (hOffsets t i).2 (hOffsets t k).2
    (hSizes t i).2 (hSizes t k).2 hSecond.
  have hBits:b=d.
    move:hBD;case:ifP=>_ /= hBD;[exact:negb_inj hBD|exact:hBD].
  have hPair:O t i=O t k.
    rewrite [O t i](surjective_pairing (O t i)) [O t k](surjective_pairing (O t k)).
    by rewrite hX hY.
  have hIndices:i=k.
    apply:val_inj;apply/eqP.
    have hUniq:uniq (if t then rev L else L) by case:ifP=>_;rewrite ?rev_uniq;exact:hPattern.2.1.
    have hSI:(i<size (if t then rev L else L))%N by case:ifP=>_;rewrite ?size_rev;exact:ltn_ord.
    have hSK:(k<size (if t then rev L else L))%N by case:ifP=>_;rewrite ?size_rev;exact:ltn_ord.
    rewrite -(@nth_uniq _ (0,0) (if t then rev L else L) i k hSI hSK hUniq).
    exact/eqP.
  by rewrite hBits hIndices.
exists e;split=>//;split.
- move=>[[b i] t];rewrite hG in_fsetM /e /=.
  apply/andP;split;exact:(hC _ _ (hOffsets t i).1).1 || exact:(hC _ _ (hOffsets t i).2).1.
- move=>[b i] p q [hp0 hp1] [hq0 hq1].
  have hBudget:=@critical_corner_pattern_index_budget n budget L hPattern i.
  have hL0:val (C false (O false i).1)=
      (`[critical_corner_coordinate r false (O false i).1,critical_corner_coordinate r false (O false i).1+1/r]:set (real_line_metric R)):=
    (hC _ _ (hOffsets false i).1).2.
  rewrite /e /= (hC _ _ (hOffsets false i).1).2 in hp0.
  rewrite /e /= (hC _ _ (hOffsets false i).2).2 in hp1.
  rewrite /e /= (hC _ _ (hOffsets true i).1).2 in hq0.
  rewrite /e /= (hC _ _ (hOffsets true i).2).2 in hq1.
  exact:(@critical_opposite_corner_square_gap R r false b
    (O false i).1 (O false i).2 (O true i).1 (O true i).2 budget p q hr hBudget hp0 hp1 hq0 hq1).
Qed.
