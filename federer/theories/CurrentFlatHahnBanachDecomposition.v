(** Federer (1969), 4.1.12, pp. 367–368: the
    original Hahn–Banach extension gives two actual
    currents supported in K. Its single product
    seminorm bound controls the sum of their masses,
    without a factor two. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothDerivativeSeminormLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormSealed
  CurrentFlatDualSeminormBasic CurrentFlatDualFiniteArithmetic CurrentFlatFiniteSupport
  CurrentFlatHahnBanach CurrentCompactZerothComass ExtendedSupremumPairBound
  CurrentMassUP CurrentMassSealed CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentBoundary CurrentEvaluation CurrentTestExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatHahnBanachDecomposition.
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
Local Notation p := (fun phi:DT=>nu K 0%N (inc phi)).
Local Notation q := (fun psi:NT=>nuNext K 0%N (incNext psi)).
Local Notation Flat := (@current_flat_test_seminorm R h2 n m U hU K).
Local Notation NextFlat := (@current_flat_test_seminorm R h2 n m.+1 U hU K).
Local Notation Dual := (@CurrentFlatDualSeminorm.value R h2 n m U hU K).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation NextM := (@CurrentMass.value R h2 n m.+1 U hU).
Local Notation d := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation boundary := (@current_boundary R h2 n m U hU).

(** Source for [current_flat_hahn_banach_decomposition]: the
    finite original F_K(T) gives T=R+boundary S,
    with both supports in K and M(R)+M(S)<=F_K(T),
    Federer 4.1.12, pp. 367–368. The coordinate
    maps are constructed only inside this existence
    proof, and represented by actual original currents. *)
Theorem current_flat_hahn_banach_decomposition (T:C) c:
  Dual (action T)=c%:E->
  exists A:C,exists B:NC,
    T=A+boundary B /\
    @current_support R h2 n U hU m A `<=` smooth_compact_carrier K /\
    @current_support R h2 n U hU m.+1 B `<=` smooth_compact_carrier K /\
    (M A+NextM B<=c%:E)%E.
Proof.
move=>hValue.
have hc:=@current_flat_dual_nonnegative R h2 n m U hU K (action T).
rewrite hValue lee_fin in hc.
have [L [hAgreement hL]]:=@current_flat_hahn_banach_extension R h2 n m U hU K (action T) c hValue.
have hLinearA:linear (fun phi:DT=>L (phi,(0:NT))).
  move=>a phi psi.
  have hPair:(a*:phi+psi,(0:NT))=a*:(phi,(0:NT))+(psi,(0:NT)).
    change ((a*:phi+psi,(0:NT))=(a*:phi+psi,a*:(0:NT)+(0:NT))).
    by rewrite scaler0 add0r.
  rewrite hPair;exact:linearP.
have hLinearB:linear (fun psi:NT=>L ((0:DT),psi)).
  move=>a phi psi.
  have hPair:((0:DT),a*:phi+psi)=a*:((0:DT),phi)+((0:DT),psi).
    change (((0:DT),a*:phi+psi)=(a*:(0:DT)+(0:DT),a*:phi+psi)).
    by rewrite scaler0 add0r.
  rewrite hPair;exact:linearP.
pose rawA:Hom DT R^o:=@HomMap R DT R^o (fun phi=>L (phi,(0:NT)))
  (introT (asboolP _) hLinearA).
pose rawB:Hom NT R^o:=@HomMap R NT R^o (fun psi=>L ((0:DT),psi))
  (introT (asboolP _) hLinearB).
have hPNonnegative:forall phi:DT,0<=p phi.
  move=>phi;exact:smooth_derivative_seminorm_nonnegative
    (smooth_function_derivative_seminorm_laws hD K 0%N) (inc phi).
have hQNonnegative:forall psi:NT,0<=q psi.
  move=>psi;exact:smooth_derivative_seminorm_nonnegative
    (smooth_function_derivative_seminorm_laws hNextD K 0%N) (incNext psi).
have hPZero:p (0:DT)=0.
  by rewrite /p linear0 (real_seminorm_zero
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hD K 0%N))).
have hQZero:q (0:NT)=0.
  by rewrite /q linear0 (real_seminorm_zero
    (smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hNextD K 0%N))).
have hABound:forall phi:DT,`|rawA phi|<=c * Flat phi.
  move=>phi;have h:=hL phi (0:NT).
  rewrite hQZero (max_idPl (hPNonnegative phi)) in h.
  apply:(le_trans h);apply:(ler_wpM2l hc).
  rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula.
  by rewrite le_max lexx.
have hBBound:forall psi:NT,`|rawB psi|<=c * NextFlat psi.
  move=>psi;have h:=hL (0:DT) psi.
  rewrite hPZero (max_idPr (hQNonnegative psi)) in h.
  apply:(le_trans h);apply:(ler_wpM2l hc).
  rewrite /current_flat_test_seminorm current_flat_form_seminorm_formula.
  by rewrite le_max lexx.
have hAFinite:=@current_flat_dual_finite_from_bound R h2 n m U hU K rawA c hc hABound.
have hBFinite:=@current_flat_dual_finite_from_bound R h2 n m.+1 U hU K rawB c hc hBBound.
have [A [hA hASupport]]:=@current_finite_flat_supported_current R h2 n m U hU K rawA hAFinite.
have [B [hB hBSupport]]:=@current_finite_flat_supported_current R h2 n m.+1 U hU K rawB hBFinite.
have hPairValue:forall phi psi,L (phi,psi)=action A phi+nextAction B psi.
  move=>phi psi.
  have hPair:(phi,psi)=(phi,(0:NT))+((0:DT),psi).
    change ((phi,psi)=(phi+0,0+psi));by rewrite addr0 add0r.
  by rewrite hPair (linD (hom_linear L)) hA hB.
exists A,B;split.
- apply:current_values_extensional=>phi.
  rewrite (linD (hom_linear action)) hom_addE current_boundary_evaluation.
  by rewrite -hPairValue hAgreement.
- split;first exact:hASupport.
  split;first exact:hBSupport.
  have hAZero:@current_mass_values R h2 n m U hU A 0.
    exists (0:DT);split;last exact:linear0.
    apply:(@current_global_comass_bound R h2 n m U _ 1).2=>x hx.
    have hZero:smooth_test_values_hom hE (0:DT)=(fun _=>0):=linear0 _.
    change (@current_form_comass R h2 n m ((smooth_test_values_hom hE (0:DT)) x)<=1).
    by rewrite hZero (real_seminorm_zero (@current_form_comass_real_norm R h2 n m).1) ler01.
  have hBZero:@current_mass_values R h2 n m.+1 U hU B 0.
    exists (0:NT);split;last exact:linear0.
    apply:(@current_global_comass_bound R h2 n m.+1 U _ 1).2=>x hx.
    have hZero:smooth_test_values_hom hNextE (0:NT)=(fun _=>0):=linear0 _.
    change (@current_form_comass R h2 n m.+1 ((smooth_test_values_hom hNextE (0:NT)) x)<=1).
    by rewrite hZero (real_seminorm_zero (@current_form_comass_real_norm R h2 n m.+1).1) ler01.
  apply:(@extended_supremum_pair_sum_bound R
    (@current_mass_values R h2 n m U hU A)
    (@current_mass_values R h2 n m.+1 U hU B) (M A) (NextM B) c
    hAZero hBZero (@CurrentMass.laws R h2 n m U hU A)
    (@CurrentMass.laws R h2 n m.+1 U hU B)).
  move=>a [phi [hPhi <-]] b [psi [hPsi <-]].
  rewrite -hPairValue.
  apply:(le_trans (ler_norm _));apply:(le_trans (hL phi psi)).
  have hMax:Num.max (p phi) (q psi)<=1.
    rewrite ge_max;apply/andP;split.
    + exact:(@current_unit_test_compact_zeroth R h2 n m U hU K phi hPhi).
    + exact:(@current_unit_test_compact_zeroth R h2 n m.+1 U hU K psi hPsi).
  have h:=ler_wpM2l hc hMax;by rewrite mulr1 in h.
Qed.
End CurrentFlatHahnBanachDecomposition.
