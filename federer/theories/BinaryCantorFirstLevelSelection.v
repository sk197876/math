(** Federer (1969), 3.3.20, pp. 306–307:
    local exhaustive indexing of the two actual first-level intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorFirstLevelIntervals BinaryCantorRatioBounds RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_first_level_coordinate]: supporting
    actual first-level lower coordinate in 3.3.20,
    pp. 306–308. The two original
    positions are zero and one minus the original side ratio. *)
Definition binary_first_level_coordinate (R:realType) (s:R) (b:bool):R:=
  if b then 1-s else 0.

(** Source for [binary_first_level_original_interval_selection]:
    the two actual original first-level intervals
    admit a local injective and exhaustive boolean
    indexing, 3.3.20, pp. 306–307.
    Every endpoint and every original member is
    retained; no replacement interval family is used. *)
Theorem binary_first_level_original_interval_selection (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  exists I:bool->compact_real_intervals R,injective I /\
    (forall b,I b \in H 1%N /\val (I b)=
      (`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R))) /\
    forall S,S \in H 1%N ->exists b,S=I b.
Proof.
move=>hc hm hm1 hJ hTree.
have hCharacter:=@binary_original_first_level_intervals R c m J H hc hm hm1 hJ hTree.
have /andP[hQuarter hSmall]:=(binary_cantor_original_ratio_bounds hm hm1).1.
have hEnd:(1-real_power 2 (-m^-1):R)+real_power 2 (-m^-1)= 1 by ring.
have hEach b:exists S:compact_real_intervals R,S \in H 1%N /\val S=
    (`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R)).
  have hOrder:binary_first_level_coordinate (real_power 2 (-m^-1)) b<=binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1) by lra.
  have hInterval:is_compact_real_interval
      (`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R)).
    exists (binary_first_level_coordinate (real_power 2 (-m^-1)) b),(binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1));by split.
  pose S:compact_real_intervals R:=Sub
    (`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R)) (mem_set hInterval).
  exists S;split=>//;apply/(hCharacter S).
  change ((`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R))=
    (`[0,real_power 2 (-m^-1)]:set (real_line_metric R)) \/
    (`[binary_first_level_coordinate (real_power 2 (-m^-1)) b,binary_first_level_coordinate (real_power 2 (-m^-1)) b+real_power 2 (-m^-1)]:set (real_line_metric R))=(`[1-real_power 2 (-m^-1),1]:set (real_line_metric R))).
  rewrite /binary_first_level_coordinate;case:ifP=>_;[right|left];by rewrite ?hEnd ?add0r.
have [I hI]:=choice hEach.
have hLeft:val (I false)=(`[0,real_power 2 (-m^-1)]:set (real_line_metric R)) by rewrite (hI false).2 /binary_first_level_coordinate add0r.
have hRight:val (I true)=(`[1-real_power 2 (-m^-1),1]:set (real_line_metric R)) by rewrite (hI true).2 /binary_first_level_coordinate hEnd.
have hDifferent:I false!=I true.
  apply/eqP=>hEqual.
  have hZero:val (I false) 0 by rewrite hLeft /=;apply/andP;split;[exact:lexx|exact:ltW hQuarter].
  rewrite hEqual hRight /= in hZero;move:hZero=>/andP[hLow _].
  change (is_true ((1-real_power 2 (-m^-1):R)<=0)) in hLow;lra.
exists I;split.
- by move=>[] [] hEqual=>//;move:hDifferent;rewrite hEqual eqxx.
split;first exact:hI.
move=>S /(hCharacter S)[hValue|hValue].
- exists false;apply:val_inj;by rewrite hValue hLeft.
- exists true;apply:val_inj;by rewrite hValue hRight.
Qed.
