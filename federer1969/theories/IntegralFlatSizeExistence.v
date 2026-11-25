(** Federer (1969), 4.1.24, p. 382: the original
    integral flat infimum exists and is finite. The
    class definition supplies a rectifiable decomposition;
    proved finite masses make its real cost finite.
    Real completeness is used only as order background.
    This witness is not a consumer definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed CurrentMassBasic
  RectifiableCurrentApproximationUP RectifiableCurrentBasic
  IntegralCurrentClassesUP IntegralFlatSizeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralFlatSizeExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation Spec:=(@is_integral_flat_size R h2 n m U hU K).

(** Source for [integral_flat_size_exists]: every actual
    original integral flat current has the finite infimum
    specified in 4.1.24, p. 382. The construction
    uses every same-K rectifiable pair, not a chosen
    presentation. It proves existence without integral attainment. *)
Theorem integral_flat_size_exists (T:C):
  @is_integral_flat_current_supported_in R h2 n U hU m K T->
  exists a:R,Spec T a.
Proof.
move=>hT.
pose cost:=fun (A:C) (S:Next)=>fine (M m A)+fine (M m.+1 S).
pose Costs:set R:=[set c|exists A:C,exists S:Next,
  Rect m A /\Rect m.+1 S /\T=A+bd S /\c=cost A S].
have hCost (A:C) (S:Next):Rect m A->Rect m.+1 S->
    (M m A+M m.+1 S=(cost A S)%:E)%E.
  move=>hA hS.
  have[a [ha hMA]]:=@current_finite_mass_value R h2 n m U hU A
    (@rectifiable_current_finite_mass R h2 n m U hU K A hA).
  have[b [hb hMS]]:=@current_finite_mass_value R h2 n m.+1 U hU S
    (@rectifiable_current_finite_mass R h2 n m.+1 U hU K S hS).
  by rewrite /cost hMA hMS /=.
have hNonempty:Costs !=set0.
  have[A [S [hA [hS hEqual]]]]:=hT.
  exists (cost A S);exists A,S;by split=>//;split=>//;split.
have hLower:lbound Costs 0.
  move=>c [A [S [hA [hS [hEqual ->]]]]].
  have hPositive:(0<=M m A+M m.+1 S)%E.
    exact:adde_ge0 (current_mass_nonnegative A) (current_mass_nonnegative S).
  by rewrite (hCost A S hA hS) lee_fin in hPositive.
have hBounded:has_lbound Costs by exists 0.
have hInf:has_inf Costs:=conj hNonempty hBounded.
exists (inf Costs);constructor.
- exact:lb_le_inf hNonempty hLower.
- move=>A S hA hS hEqual;rewrite (hCost A S hA hS) lee_fin.
  apply:(ge_inf hBounded);exists A,S;by split=>//;split=>//;split.
- move=>epsilon hEpsilon.
  have[c [A [S [hA [hS [hEqual hValue]]]]] hClose]:=inf_adherent hEpsilon hInf.
  exists A,S;split;first exact:hA.
  split;first exact:hS.
  split;first exact:hEqual.
  rewrite (hCost A S hA hS) lte_fin.
  by rewrite -hValue.
Qed.
End IntegralFlatSizeExistence.
