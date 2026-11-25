(** Federer (1969), 4.1.7, p. 359:
    the actual half-line example agrees with
    the coordinate-oriented Lebesgue current on
    every original open region lying below b.
    The original subset integrals and exact
    test zero extensions prove this directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct FiniteExteriorPowers AlternatingForms AlternatingPairing AlternatingIsomorphism
  CurrentSpaces CurrentCoefficientNorms CurrentOpenRestriction CurrentOpenConstantDensity EuclideanFundamentalCurrent
  HalflineCurrents SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral SummableRealFunctionUP
  RealSubsetIntegralGraph EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineOpenRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation mu := (@euclidean_lebesgue_measure R 1).
Local Notation top := (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).
Variable b:R.
Variable A:set X.
Hypothesis hA:forall x,A x->norm_domain_interior NX A x.
Arguments hA : clear implicits.
Hypothesis hAU:forall x,A x->U x.
Arguments hAU : clear implicits.
Hypothesis hAb:forall x,A x->x ord0<=b.
Arguments hAb : clear implicits.
Local Notation P := (@current_open_test_extension R h2 1 1%N A U hA hU hAU).

(** Source for [halfline_current_open_restriction]:
    on every original open subset of
    (0,b), the actual example T is
    E^1 restricted to that subset,
    supporting its exact support in Federer
    4.1.7, p. 359. The same
    conclusion holds for every open subset
    of (0,b] through the original action. *)
Theorem halfline_current_open_restriction:
  @current_open_restriction R h2 1 1%N A U hA hU hAU (@halfline_current R h2 b)=
    @euclidean_fundamental_current_open R h2 1 A hA.
Proof.
apply:(@current_values_extensional R h2 1 1%N A hA)=>phi.
rewrite current_open_restriction_evaluation.
pose f x:=pairing top (@current_test_value R h2 1 A hA 1%N phi x).
have hOutside x:~A x->f x=0.
  move=>hx.
  have hZero:@current_test_value R h2 1 A hA 1%N phi x=0:=
    (@smooth_test_value_outside R X (A_m X R^o 1) NX
    (@current_form_comass R h2 1 1%N) hNX (@current_form_comass_real_norm R h2 1 1%N) A
    (@current_smooth_space R h2 1 A hA 1%N) (@current_smooth_value R h2 1 A hA 1%N)
    (@current_smooth_space_laws R h2 1 A hA 1%N) phi x hx).
  by rewrite /f hZero /pairing linear0 hom_zeroE.
have hOutsideInterval (x:X):~(0<x ord0<=b)->f x=0.
  move=>hx;apply:hOutside=>hAx;apply:hx;apply/andP;split.
  - exact:(hAU x hAx).
  - exact:(hAb x hAx).
have hOriginal:=@halfline_current_action R h2 b (P phi).
have hValues:(fun x=>pairing top (@current_test_value R h2 1 U hU 1%N (P phi) x))=f.
  apply:funext=>x;by rewrite current_open_test_extension_values.
rewrite hValues in hOriginal.
have hLeft:=(@real_subset_integral_total R X mu [set x:X|0<x ord0<=b] f f _
  (fun _ _=>erefl) hOutsideInterval).1 hOriginal.
have hOriginalE:=@current_open_constant_density_action R h2 1 1%N A hA top phi.
have hRight:=(@real_subset_integral_total R X mu A f f _ (fun _ _=>erefl) hOutside).1 hOriginalE.
exact:(EFin_inj (measure_integral_unique hLeft hRight)).
Qed.
End HalflineOpenRestriction.
