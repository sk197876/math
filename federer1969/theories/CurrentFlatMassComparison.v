(** Federer (1969), 4.1.12, pp. 367–368: mass
    bounds the original flat seminorm for currents
    supported in K. Every supported decomposition
    gives the reverse side of the printed minimum
    formula, including infinite masses. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothTestSpaces CurrentFlatNorm
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  CurrentCompactMassAction CurrentMassSealed CurrentMassBasic
  CurrentBoundary CurrentBoundarySupport CurrentTestExteriorDerivative
  CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatMassComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation NT := (@current_test_space R h2 n U hU m.+1).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation NC := (@current_space R h2 n U hU m.+1).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation nextAction := (@current_value R h2 n U hU m.+1).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hNextE := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hNextD := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation incNext := (smooth_test_inclusion hNextE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation nuNext := (smooth_function_derivative_seminorm hNextD).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation NextM := (@CurrentMass.value R h2 n m.+1 U hU).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation boundary := (@current_boundary R h2 n m U hU).

(** Source for [current_flat_norm_le_mass]: the original
    flat seminorm is no greater than mass for a
    current supported in K, supporting Federer 4.1.12,
    pp. 367–368. Infinite mass is retained. *)
Theorem current_flat_norm_le_mass (T:C):
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  (F T<=M T)%E.
Proof.
move=>hSupport.
case:(ltP (M T) (+oo)%E)=>hFinite;last exact:le_trans (leey (F T)) hFinite.
have [a [ha hValue]]:=@current_finite_mass_value R h2 n m U hU T hFinite.
rewrite hValue /current_flat_norm.
apply:(@current_flat_dual_upper_from_bound R h2 n m U hU K (action T) a ha)=>phi.
have hBound:=@current_compact_mass_action_bound R h2 n m U hU K T a hValue hSupport phi.
apply:(le_trans hBound);apply:(ler_wpM2l ha).
rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula.
by rewrite le_max lexx.
Qed.

(** Source for [current_flat_decomposition_lower_bound]:
    every original S supported in K satisfies
    F_K(T)<=M(T-boundary S)+M(S) when T is supported
    in K, Federer 4.1.12, pp. 367–368. No
    finiteness premise is added to this assertion. *)
Theorem current_flat_decomposition_lower_bound (T:C) (S:NC):
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  @current_support R h2 n U hU m.+1 S `<=` smooth_compact_carrier K->
  (F T<=M ((T-boundary S)%R)+NextM S)%E.
Proof.
move=>hT hS.
pose A:=T-boundary S.
have hBoundarySupport:@current_support R h2 n U hU m (boundary S) `<=` smooth_compact_carrier K.
  move=>x hx;exact:hS x (@current_boundary_support_subset R h2 n m U hU S x hx).
have hASupport:@current_support R h2 n U hU m A `<=` smooth_compact_carrier K.
  have h:=@current_support_linear_subset R h2 n m U hU K (-1) (boundary S) T hBoundarySupport hT.
  by rewrite scaleN1r addrC in h.
case:(ltP (M A+NextM S)%E (+oo)%E)=>hCost;last exact:le_trans (leey (F T)) hCost.
have hAFinite:(M A < +oo)%E.
  exact:le_lt_trans (leeDl (M A) (@current_mass_nonnegative R h2 n m.+1 U hU S)) hCost.
have hSFinite:(NextM S < +oo)%E.
  exact:le_lt_trans (leeDr (NextM S) (@current_mass_nonnegative R h2 n m U hU A)) hCost.
have [a [ha hAValue]]:=@current_finite_mass_value R h2 n m U hU A hAFinite.
have [b [hb hBValue]]:=@current_finite_mass_value R h2 n m.+1 U hU S hSFinite.
rewrite hAValue hBValue -EFinD /current_flat_norm.
apply:(@current_flat_dual_upper_from_bound R h2 n m U hU K (action T) (a+b)
  (addr_ge0 ha hb))=>phi.
have hA:=@current_compact_mass_action_bound R h2 n m U hU K A a hAValue hASupport phi.
have hB:=@current_compact_mass_action_bound R h2 n m.+1 U hU K S b hBValue hS (d phi).
have hFirst:nu K 0%N (inc phi)<=Flat phi.
  rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula;by rewrite le_max lexx.
have hSecond:nuNext K 0%N (incNext (d phi))<=Flat phi.
  rewrite current_test_exterior_derivative_inclusion /current_flat_test_seminorm
    current_flat_form_seminorm_formula;by rewrite le_max lexx orbT.
have hDecomposition:T=A+boundary S by rewrite /A subrK.
have hAction:action T phi=action A phi+nextAction S (d phi).
  by rewrite hDecomposition (linD (hom_linear action)) hom_addE current_boundary_evaluation.
rewrite hAction mulrDl.
apply:(le_trans (ler_normD _ _));apply:lerD.
- exact:le_trans hA (ler_wpM2l ha hFirst).
- exact:le_trans hB (ler_wpM2l hb hSecond).
Qed.
End CurrentFlatMassComparison.
