(** Federer (1969), 3.3.20, pp. 306–308:
    local exhaustive indexing of the two actual first-level intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  CriticalFirstLevelIntervals RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_first_level_coordinate]: supporting
    actual first-level lower coordinate in 3.3.20,
    pp. 306–308. The two original
    positions are zero and three quarters. *)
Definition critical_first_level_coordinate (R:realType) (b:bool):R:=
  if b then 3/4 else 0.

(** Source for [critical_first_level_original_interval_selection]:
    the two actual original first-level intervals
    admit a local injective and exhaustive boolean
    indexing, 3.3.20, pp. 306–308.
    Every endpoint and every original member is
    retained; no replacement interval family is used. *)
Theorem critical_first_level_original_interval_selection (R:realType) (c:R)
    (J:compact_real_intervals R) H:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  exists I:bool->compact_real_intervals R,injective I /\
    (forall b,I b \in H 1%N /\val (I b)=
      (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R))) /\
    forall S,S \in H 1%N ->exists b,S=I b.
Proof.
move=>hc hJ hTree.
have hCharacter:=@critical_original_first_level_intervals R c J H hc hJ hTree.
have hQuarter:0<(1/4:R) by rewrite divr_gt0 // ltr0n.
have hEnd:(3/4:R)+1/4= 1 by field;rewrite ?pnatr_eq0.
have hEach b:exists S:compact_real_intervals R,S \in H 1%N /\val S=
    (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R)).
  have hOrder:critical_first_level_coordinate R b<=critical_first_level_coordinate R b+1/4 by lra.
  have hInterval:is_compact_real_interval
      (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R)).
    exists (critical_first_level_coordinate R b),(critical_first_level_coordinate R b+1/4);by split.
  pose S:compact_real_intervals R:=Sub
    (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R)) (mem_set hInterval).
  exists S;split=>//;apply/(hCharacter S).
  change ((`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R))=
    (`[0,1/4]:set (real_line_metric R)) \/
    (`[critical_first_level_coordinate R b,critical_first_level_coordinate R b+1/4]:set (real_line_metric R))=(`[3/4,1]:set (real_line_metric R))).
  rewrite /critical_first_level_coordinate;case:ifP=>_;[right|left];by rewrite ?hEnd ?add0r.
have [I hI]:=choice hEach.
have hLeft:val (I false)=(`[0,1/4]:set (real_line_metric R)) by rewrite (hI false).2 /critical_first_level_coordinate add0r.
have hRight:val (I true)=(`[3/4,1]:set (real_line_metric R)) by rewrite (hI true).2 /critical_first_level_coordinate hEnd.
have hDifferent:I false!=I true.
  apply/eqP=>hEqual.
  have hZero:val (I false) 0 by rewrite hLeft /=;apply/andP;split;[exact:lexx|exact:ltW hQuarter].
  rewrite hEqual hRight /= in hZero;move:hZero=>/andP[hLow _].
  change (is_true ((3/4:R)<=0)) in hLow;lra.
exists I;split.
- by move=>[] [] hEqual=>//;move:hDifferent;rewrite hEqual eqxx.
split;first exact:hI.
move=>S /(hCharacter S)[hValue|hValue].
- exists false;apply:val_inj;by rewrite hValue hLeft.
- exists true;apply:val_inj;by rewrite hValue hRight.
Qed.
