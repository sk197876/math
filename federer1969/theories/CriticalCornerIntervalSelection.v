(** Federer (1969), 3.3.20, pp. 308–309:
    local actual interval witnesses for all corner offsets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  CriticalCornerCoordinate CriticalCantorCornerIntervals RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_critical_corner_interval_selection]: independent
    original membership and exact endpoint laws for
    the corner intervals used in 3.3.20,
    pp. 308–309. No injection, pair separation,
    missing-count estimate or measure conclusion is assumed. *)
Definition is_critical_corner_interval_selection (R:realType) (r:R)
    (F:{fset compact_real_intervals R}) (C:bool->nat->compact_real_intervals R):Prop:=
  forall b p,p \in [::0;3;12;15] ->C b p \in F /\
    val (C b p)=(`[critical_corner_coordinate r b p,
      critical_corner_coordinate r b p+1/r]:set (real_line_metric R)).

(** Source for [critical_corner_original_interval_selection_exists]:
    the actual corner intervals for every offset
    used by 3.3.20, pp. 308–309,
    admit a local simultaneous selection. Original
    address membership proves all laws; no global
    auxiliary selection or replacement tree is introduced. *)
Theorem critical_corner_original_interval_selection_exists (R:realType) (c:R)
    (J:compact_real_intervals R) H j:
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  (2<=j)%N ->exists C,is_critical_corner_interval_selection ((4:R)^+j) (H j) C.
Proof.
move=>hc hJ hTree hj.
have hExists (k:bool*nat):exists S:compact_real_intervals R,
    k.2 \in [::0;3;12;15] ->S \in H j /\
      val S=(`[critical_corner_coordinate ((4:R)^+j) k.1 k.2,
        critical_corner_coordinate ((4:R)^+j) k.1 k.2+1/(4:R)^+j]:set (real_line_metric R)).
  case:(boolP (k.2 \in [::0;3;12;15]))=>[hp|hp].
  - have [L [U [hL [hU [hLV hUV]]]]]:=@critical_cantor_original_corner_intervals R c J H j k.2
      hc hJ hTree hj hp.
    case:k hp hLV hUV=>[[] p] /= hp hLV hUV.
    + exists U;move=>_;split=>//.
      have hEnd:critical_corner_coordinate ((4:R)^+j) true p+1/(4:R)^+j= 1-p%:R/(4:R)^+j.
        rewrite /critical_corner_coordinate natrD;ring.
      by rewrite hEnd /critical_corner_coordinate.
    + exists L;move=>_;split=>//.
      have hEnd:critical_corner_coordinate ((4:R)^+j) false p+1/(4:R)^+j=(p+1)%:R/(4:R)^+j.
        rewrite /critical_corner_coordinate natrD;ring.
      by rewrite hEnd /critical_corner_coordinate.
  - exists J;move=>hP;discriminate hP.
have [C hC]:=choice hExists.
exists (fun b p=>C (b,p));move=>b p hp;exact:hC (b,p) hp.
Qed.

(** Source for [critical_corner_interval_selection_injective]:
    distinct original corner offsets give distinct actual
    intervals, supporting the pairwise distinct squares in
    3.3.20, pp. 308–309. Endpoint uniqueness
    and separated corner strips prove this consequence
    of the independent selection laws. *)
Lemma critical_corner_interval_selection_injective (R:realType) (r:R)
    (F:{fset compact_real_intervals R}) C:
  is_critical_corner_interval_selection r F C ->0<r ->
  forall b d a c,a \in [::0;3;12;15] ->c \in [::0;3;12;15] ->
  ((a+1)%:R:R)/r<=1/4 ->((c+1)%:R:R)/r<=1/4 ->
  C b a=C d c ->b=d /\a=c.
Proof.
move=>hC hr b d a c ha hc hASize hCSize hEqual.
apply:(@critical_corner_interval_endpoints_unique R r b d a c hr hASize hCSize).
by rewrite -(hC b a ha).2 -(hC d c hc).2 hEqual.
Qed.
