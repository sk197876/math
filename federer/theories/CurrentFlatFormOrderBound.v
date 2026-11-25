(** Federer (1969), 4.1.12, p. 367: the
    original F_K is controlled by the order-one smooth
    seminorm on the same K. Use the actual first-order
    exterior derivative and preceding compact bounds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms OpenFamilyTopologyUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  SmoothTestTopology CurrentCoefficientNorms CurrentSpaces CurrentExteriorDifferentialMap
  SmoothCurrentExteriorDerivative SmoothFirstOrderUP SmoothFirstOrderSealed SmoothFirstOrderSupport
  SupportedSmoothOperatorTests ExteriorDerivativeUP SmoothFirstOrderSeminormBound
  SmoothFunctionTopology SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws CurrentFlatFormSeminormSealed CurrentFlatFormSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatFormOrderBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation Z := (A_m X R^o m.+1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (@current_form_comass R h2 n m.+1).
Local Notation hNZ := (@current_form_comass_real_norm R h2 n m.+1).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation F := (@current_smooth_space R h2 n U hU m.+1).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation fv := (@current_smooth_value R h2 n U hU m.+1).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation hF := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation D := (@current_smooth_derivatives R h2 n U hU m).
Local Notation G := (@current_smooth_derivatives R h2 n U hU m.+1).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hG := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation L := (@current_exterior_differential_map R h2 n m).
Local Notation hL := (@current_exterior_differential_map_bounded R h2 n m).
Local Notation P := (@smooth_current_exterior_derivative R h2 n m U hU).
Local Notation hP := (@SmoothFirstOrder.laws R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hE hF D hD L hL).
Local Notation hSupport := (@smooth_first_order_preserves_support R X Y Z NX NY NZ hNX hNY hNZ
  U hU E F ev fv hE hF D hD L P hP).

Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation nuNext := (smooth_function_derivative_seminorm hG).
Local Notation Flat := (@CurrentFlatFormSeminorm.value R h2 n m U hU).

(** Source for [current_flat_form_order_one_bound]: the original
    flat seminorm has a finite bound by nu_K^1 on the
    same compact K, supporting the finite-flat continuity
    assertion in Federer 4.1.12, p. 367. Reuse the
    preceding actual exterior-derivative seminorm bound. *)
Theorem current_flat_form_order_one_bound (K:smooth_compact_set hNX U):
  exists C:R,0<=C /\forall phi,Flat K phi<=C * nu K 1%N phi.
Proof.
have [C [hC hDerivative]]:=@smooth_first_order_seminorm_bound R X Y Z NX NY NZ hNX hNY hNZ
  U E F ev fv hF D G hD hG L hL P hP K 0%N (nu K 1%N) (nuNext K 0%N)
  (smooth_function_derivative_seminorm_laws hD K 1%N)
  (smooth_function_derivative_seminorm_laws hG K 0%N).
exists (C+1);split;first exact:addr_ge0 hC ler01.
move=>phi.
have hZero:=@smooth_derivative_seminorm_monotone R X Y NX NY hNX hNY U E D K 0%N
  (nu K 0%N) (smooth_function_derivative_seminorm_laws hD K 0%N)
  K 1%N (nu K 1%N) (smooth_function_derivative_seminorm_laws hD K 1%N)
  (leq0n 1%N) (fun _ hx=>hx) phi.
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hD K 1%N) phi.
have hNext:=hDerivative phi.
rewrite current_flat_form_seminorm_formula ge_max;apply/andP;split;nra.
Qed.
End CurrentFlatFormOrderBound.
