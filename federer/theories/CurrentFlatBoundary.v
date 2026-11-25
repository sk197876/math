(** Federer (1969), 4.1.12, p. 367: the
    original flat seminorm does not increase under
    the boundary. The preceding actual identity
    d squared zero supplies the exact constant one. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothTestSpaces CurrentFlatNorm
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  CurrentTestExteriorDerivative CurrentExteriorDerivativeSquared CurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatBoundary.
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
Local Notation NNT := (@current_test_space R h2 n U hU m.+2).
Local Notation NC := (@current_space R h2 n U hU m.+1).
Local Notation hNextE := (@current_smooth_space_laws R h2 n U hU m.+1).
Local Notation hNextNextE := (@current_smooth_space_laws R h2 n U hU m.+2).
Local Notation incNext := (smooth_test_inclusion hNextE).
Local Notation incNextNext := (smooth_test_inclusion hNextNextE).
Local Notation hNextD := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation hNextNextD := (@current_smooth_derivative_laws R h2 n U hU m.+2).
Local Notation nuNext := (smooth_function_derivative_seminorm hNextD).
Local Notation nuNextNext := (smooth_function_derivative_seminorm hNextNextD).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation NextFlat := (@current_flat_test_seminorm R h2 n m.+1 U hU K).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation NextF := (@current_flat_norm R h2 n m.+1 U hU K).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation boundary := (@current_boundary R h2 n m U hU).

(** Source for [current_flat_test_derivative_bound]:
    F_K(d phi)<=F_K(phi) on actual original tests,
    supporting the boundary estimate in Federer
    4.1.12, p. 367. The next exterior
    derivative is zero; the compact K is unchanged. *)
Lemma current_flat_test_derivative_bound (phi:DT):NextFlat (d phi)<=Flat phi.
Proof.
have hZero:nuNextNext K 0%N (incNextNext (0:NNT))=0.
  by rewrite linear0 (real_seminorm_zero
    (smooth_derivative_seminorm_is_seminorm
      (smooth_function_derivative_seminorm_laws hNextNextD K 0%N))).
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hNextD K 0%N) (incNext (d phi)).
rewrite /current_flat_test_seminorm !current_flat_form_seminorm_formula
  -!current_test_exterior_derivative_inclusion current_test_exterior_derivative_squared hZero
  (max_idPl hNonnegative).
by rewrite le_max lexx orbT.
Qed.

(** Source for [current_flat_boundary_bound]: the
    exact original F_K(boundary T)<=F_K(T), Federer
    4.1.12, p. 367. The input has positive
    degree, and infinite flat values are permitted. *)
Theorem current_flat_boundary_bound (T:NC):(F (boundary T)<=NextF T)%E.
Proof.
case:(ltP (NextF T) (+oo)%E)=>hFinite;last exact:le_trans (leey (F (boundary T))) hFinite.
have [c [hc hValue]]:=@current_flat_dual_finite_value R h2 n m.+1 U hU K
  (@current_value R h2 n U hU m.+1 T) hFinite.
have hNextValue:NextF T=c%:E:=hValue.
rewrite hNextValue /current_flat_norm.
apply:(@current_flat_dual_upper_from_bound R h2 n m U hU K
  (@current_value R h2 n U hU m (boundary T)) c hc)=>phi.
rewrite current_boundary_evaluation.
apply:(le_trans (@current_flat_dual_finite_bound R h2 n m.+1 U hU K
  (@current_value R h2 n U hU m.+1 T) c hValue (d phi))).
exact:(ler_wpM2l hc (current_flat_test_derivative_bound phi)).
Qed.
End CurrentFlatBoundary.
