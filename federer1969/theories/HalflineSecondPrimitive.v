(** Federer (1969), 4.1.7, p. 359:
    the second whole-line primitive is the
    negative oriented integral from b to
    infinity. It differs from the first
    by the whole-line fundamental current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import CurrentDensityUP Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces CurrentBoundary CurrentDensityAction CurrentDensityArithmetic CurrentPointEvaluation CurrentDiracDensity
  EuclideanFundamentalCurrent HalflineCurrents HalflinePrimitiveBoundary
  EuclideanLebesgueDimensions CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureSubsetIntegral RealSubsetIntegralGraph SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineSecondPrimitive.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation C := (@full_current_space R h2 1 1%N).
Local Notation value := (@current_test_value R h2 1 (fun _=>True) hFull 1%N).
Local Notation action := (@current_value R h2 1 (fun _=>True) hFull 1%N).
Local Notation left := (@halfline_left_primitive_candidate R h2).
Local Notation fundamental := (@euclidean_fundamental_current R h2 1).
Local Notation mu := (@euclidean_lebesgue_measure R 1).
Local Notation hm := (euclidean_lebesgue_is_measure R 1).
Local Notation unit := (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).

(** Source for [halfline_right_primitive_candidate]:
    the second actual whole-line primitive,
    Federer 4.1.7, p. 359. Its
    independent definition assumes no boundary
    or uniqueness property. *)
Definition halfline_right_primitive_candidate b:C:=left b-fundamental.

(** Source for [halfline_right_primitive_boundary]:
    this additional actual primitive has
    boundary delta_b. It witnesses the
    failure of the bare uniqueness phrase
    in Federer 4.1.7, p. 359. *)
Theorem halfline_right_primitive_boundary b:
  @current_boundary R h2 1 0%N (fun _=>True) hFull
    (halfline_right_primitive_candidate b)=
  @full_dirac_current R h2 1 (euclidean_one_embed b).
Proof.
have hLinear:@current_boundary R h2 1 0%N (fun _=>True) hFull (left b-fundamental)=
    @current_boundary R h2 1 0%N (fun _=>True) hFull (left b)-
    @current_boundary R h2 1 0%N (fun _=>True) hFull fundamental.
  exact:linearB.
have hLeft:=@halfline_left_primitive_boundary R h2 b.
have hZero:=@euclidean_fundamental_current_boundary_zero R h2 0%N.
exact:(eq_trans hLinear (eq_trans
  (congr2 (fun V W:@full_current_space R h2 1 0%N=>V-W) hLeft hZero) (subr0 _))).
Qed.

(** Source for [halfline_right_primitive_action]:
    minus the second primitive integrates the
    original oriented coefficient over (b,infinity).
    This explicit counterexample supplements the
    uniqueness phrase in Federer 4.1.7,
    p. 359. The ordinary
    subset integral exists for every original
    compact test. *)
Theorem halfline_right_primitive_action b psi:
  is_measure_subset_integral mu [set x:X|b<x ord0]
    (real_total_integrand (fun x=>pairing unit (value psi x)))
    (-action (halfline_right_primitive_candidate b) psi)%:E.
Proof.
pose s:=@CharacteristicFunction.value R X (@current_halfline_upper_set R b).
have hs:=@CharacteristicFunction.laws R X (@current_halfline_upper_set R b).
have hLeft:=@halfline_left_primitive_candidate_action R h2 b.
have hFundamental:=@euclidean_fundamental_current_action R h2 1.
have hNegative:=@current_density_scaled_action R h2 1 1%N mu hm
  (fun _=>unit) fundamental (-1) hFundamental.
have hDifference:=@current_density_sum_action R h2 1 1%N mu hm
  (fun x=>s x*:unit) (fun _=>(-1)*:unit) (left b) ((-1)*:fundamental)
  hLeft hNegative.
rewrite scaleN1r in hDifference.
have hOpposite:=@current_density_scaled_action R h2 1 1%N mu hm
  (fun x=>s x*:unit+(-1)*:unit) (halfline_right_primitive_candidate b) (-1) hDifference.
have hAction:=hOpposite psi.
have hNegativeValue:action ((-1)*:halfline_right_primitive_candidate b) psi=
    -action (halfline_right_primitive_candidate b) psi.
  rewrite scaleN1r.
  exact:(@current_value_negate R h2 1 1%N (fun _=>True) hFull
    (halfline_right_primitive_candidate b) psi).
rewrite hNegativeValue in hAction.
pose g x:=pairing ((-1)*:(s x*:unit+(-1)*:unit)) (value psi x).
apply:(@real_subset_integral_total R X mu [set x:X|b<x ord0]
  (fun x=>pairing unit (value psi x)) g _ _ _).2 hAction.
- move=>x hx.
  have hOutside:~@current_halfline_upper_set R b x.
    move=>hxb;have hFalse:=lt_le_trans hx hxb;by rewrite ltxx in hFalse.
  by rewrite /g /s (characteristic_off_set hs hOutside) scale0r add0r !scaleN1r opprK.
- move=>x hx.
  have hInside:@current_halfline_upper_set R b x.
    change (is_true (x ord0<=b)).
    rewrite leNgt;apply/negP;exact:hx.
  have hVector:(-1)*:(s x*:unit+(-1)*:unit)=0.
    rewrite /s (characteristic_on_set hs hInside) scale1r.
    by rewrite !scaleN1r subrr oppr0.
  by rewrite /g hVector /pairing linear0.
Qed.
End HalflineSecondPrimitive.
