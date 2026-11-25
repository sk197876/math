(** Federer (1969), 3.4.4, p. 318: the first
    original binary interval separation and its sharp distance bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  RecurrentContraction BinaryCantorCodingUP BinaryCantorCodingLaws
  BinaryCantorAddressUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_first_split]: the choice of
    j in the second paragraph of 3.4.4, p. 318.
    Distinct original Cantor points first occupy different children
    of one original interval. Geometric decay proves existence;
    natural well ordering proves minimality. The exact printed
    gap coefficient follows from the original endpoint laws. *)
Theorem binary_original_first_split (R:realType) (rho:R) J H I a A:
  is_binary_original_coding rho J H I a ->is_special_interval_tree_limit H A ->
  0<rho ->0<1-2*rho ->forall (x y:real_line_metric R),
  A x ->A y ->x!=y ->exists w b c,b!=c /\
    val (I (rcons w b)) x /\val (I (rcons w c)) y /\
    (1-2*rho)*rho^+(size w)<=`|x-y|.
Proof.
move=>hCode hA hRho hGap x y hx hy hNe.
have hUpper:rho<=1 by nra.
have hRhoUpper:rho<1 by nra.
have hX j:=@binary_original_point_address_exists R rho J H I a A hCode hA x hx j.
have hY j:=@binary_original_point_address_exists R rho J H I a A hCode hA y hy j.
have [u hu]:=choice hX.
have [v hv]:=choice hY.
have hDistance:0<`|x-y| by rewrite normr_gt0 subr_eq0.
have hContraction:0<rho<1 by apply/andP;split.
have [N hSmall]:=@geometric_contraction_small R rho 1 `|x-y| hContraction ler01 hDistance.
rewrite mulr1 in hSmall.
have hDifferent:exists j,u j!=v j.
  exists N;apply/eqP=>hEqual.
  have hBoth:val (I (u N)) y by rewrite hEqual;exact:(hv N).2.
  have hBound:=@binary_original_coding_point_distance R rho J H I a hCode (u N) x y (hu N).2 hBoth.
  rewrite (hu N).1 in hBound.
  have hFalse:=lt_le_trans hSmall hBound;by rewrite ltxx in hFalse.
have [j hJ hMinimal]:=ex_minnP hDifferent.
have hPositive:(0<j)%N.
  case:j hJ hMinimal=>[|j] hJ hMinimal;last by [].
  have hU:u 0%N=[::] by apply/eqP;rewrite -size_eq0;apply/eqP;exact:(hu 0%N).1.
  have hV:v 0%N=[::] by apply/eqP;rewrite -size_eq0;apply/eqP;exact:(hv 0%N).1.
  by rewrite hU hV eqxx in hJ.
case:j hJ hMinimal hPositive=>[//|j] hJ hMinimal _.
have hParent:u j=v j.
  apply/eqP;apply/negPn/negP=>hBad.
  have hBack:=hMinimal j hBad.
  have hFalse:=leq_ltn_trans hBack (ltnSn j);by rewrite ltnn in hFalse.
have [b hB]:=@binary_original_point_address_step R rho J H I a hCode hRho hGap
  j (u j) (u j.+1) x (hu j).1 (hu j.+1).1 (hu j).2 (hu j.+1).2.
have [c hC]:=@binary_original_point_address_step R rho J H I a hCode hRho hGap
  j (v j) (v j.+1) y (hv j).1 (hv j.+1).1 (hv j).2 (hv j.+1).2.
have hBits:b!=c.
  apply/eqP=>hSame.
  by rewrite hB hC hParent hSame eqxx in hJ.
have hLeft:val (I (rcons (u j) b)) x by rewrite -hB;exact:(hu j.+1).2.
have hRight:val (I (rcons (u j) c)) y by rewrite hParent -hC;exact:(hv j.+1).2.
exists (u j),b,c;split=>//;split=>//;split=>//.
clear hB hC.
case:b c hBits hLeft hRight=>[|][|] // _ hLeft hRight.
- have h:=(@binary_original_coding_sibling_gap R rho J H I a hCode (u j) y x hRight hLeft).2.
  have hOpp:(y-x:R)= -(x-y) by rewrite opprB.
  by rewrite hOpp normrN in h.
- exact:(@binary_original_coding_sibling_gap R rho J H I a hCode (u j) x y hLeft hRight).2.
Qed.
