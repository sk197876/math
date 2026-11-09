(** Federer (1969), 3.4.4, p. 318: prove that
    finite binary addresses index exactly the original interval levels. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalRefinement EqualCostIntervalFamilyUP BinaryCantorIntervalChildren
  BinaryCantorAddressCoordinates BinaryCantorCodingUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_coding_exists]: the original
    interval correspondence underlying 3.4.4, p. 318. A
    finite address recursion constructs endpoint witnesses. The actual
    Phi child laws prove that these, and only these, are the
    original intervals at every level. This proves a coding of
    the original construction, without defining a substitute Cantor set. *)
Theorem binary_original_coding_exists (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J (fun _:nat=>2%N) H ->
  exists I a,is_binary_original_coding (real_power 2 (-m^-1)) J H I a.
Proof.
move=>hc hm hm1 hJ hTree.
pose rho:=real_power (2:R) (-m^-1).
have hTwo:0<(2:R) by rewrite ltr0n.
have hRho:0<rho:=@real_power_strictly_positive R 2 (-m^-1) hTwo.
have [a [hA0 [hCons hExt]]]:=binary_cantor_address_coordinates_exists rho.
have hPositive (w:seq bool):0<rho^+(size w) by rewrite exprn_gt0.
have hInterval w:is_compact_real_interval
    (`[a w,a w+rho^+(size w)]:set (real_line_metric R)).
  exists (a w),(a w+rho^+(size w));split;last reflexivity.
  have h:=ltW (hPositive w);lra.
pose I w:compact_real_intervals R:=Sub
  (`[a w,a w+rho^+(size w)]:set (real_line_metric R)) (mem_set (hInterval w)).
have hValue w:val (I w)=(`[a w,a w+rho^+(size w)]:set (real_line_metric R)) by [].
have hI0:I [::]=J.
  apply:val_inj;by rewrite hValue hA0 expr0 add0r hJ.
have hLeft w:val (I (rcons w false))=
    (`[a w,a w+rho^+(size w)*rho]:set (real_line_metric R)).
  by rewrite hValue hExt /= mul0r addr0 size_rcons exprSr.
have hRight w:val (I (rcons w true))=
    (`[a w+rho^+(size w)-rho^+(size w)*rho,a w+rho^+(size w)]:set (real_line_metric R)).
  rewrite hValue hExt /= size_rcons exprSr.
  have hLow:(a w+(1-rho)*rho^+(size w):R)=a w+rho^+(size w)-rho^+(size w)*rho by ring.
  have hUp:(a w+(1-rho)*rho^+(size w)+rho^+(size w)*rho:R)=a w+rho^+(size w) by ring.
  by rewrite hUp hLow.
have hChildren w F (hF:is_equal_cost_interval_family (fun t=>c*real_power t m) (I w) 2 F):
    forall S,S \in F <->S=I (rcons w false) \/S=I (rcons w true).
  have hLess:a w<a w+rho^+(size w) by rewrite ltrDl;exact:hPositive.
  have hChar:=@binary_cantor_interval_children R c m (a w) (a w+rho^+(size w))
    (I w) F hc hm hm1 hLess (hValue w) hF.
  have hDifference:(a w+rho^+(size w)-a w:R)=rho^+(size w) by ring.
  rewrite hDifference in hChar;cbn zeta in hChar.
  move=>S;split.
  - move=>/(hChar S)[hS|hS].
    + left;apply:val_inj;by rewrite hS hLeft.
    + right;apply:val_inj;by rewrite hS hRight.
  - move=>[->|->];apply/(hChar _);[left|right];[exact:hLeft|exact:hRight].
have hLevels j:forall S,S \in H j <->exists w,size w=j /\I w=S.
  elim:j=>[|j ih] S.
  - rewrite (equal_cost_tree_root hTree) in_fset1;split.
    + move/eqP=>->;exists [::];by split.
    + move=>[w [hw <-]].
      have hW:w=[::].
        apply/eqP;rewrite -size_eq0;apply/eqP;exact:hw.
      by rewrite hW hI0 eqxx.
  - have [F [hF hStep]]:=equal_cost_tree_step hTree j.
    rewrite hStep;split.
    + move/special_interval_refinement_membership=>[P [hP hSP]].
      have [w [hw hIP]]:=(ih P).1 hP.
      have hFP:is_equal_cost_interval_family (fun t=>c*real_power t m) (I w) 2 (F P).
        by rewrite hIP;exact:hF P hP.
      have [hS|hS]:=(hChildren w (F P) hFP S).1 hSP;
        [exists (rcons w false)|exists (rcons w true)];split;by rewrite ?size_rcons ?hw.
    + move=>[w [hw hIS]].
      case/lastP:w hw hIS=>[|v b] hw hIS;first by [].
      have hv:size v=j by move:hw;rewrite size_rcons=>/succn_inj.
      have hP:I v \in H j by apply/(ih (I v));exists v;by split.
      apply/special_interval_refinement_membership;exists (I v);split;first exact:hP.
      apply/(hChildren v (F (I v)) (hF (I v) hP) S).
      clear hw;case:b hIS=>hIS;[right|left];exact:esym hIS.
exists I,a;constructor;[by split|exact:hValue|exact:hExt|exact:hLevels].
Qed.
