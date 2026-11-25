(** Federer (1969), 4.1.18, p. 374: existence of
    the original averaging zero-current. The public smooth
    Lebesgue-density map supplies an actual continuous current;
    no integral in the nonnormed current space is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading
  AlternatingForms AlternatingZero AlternatingPairing PairingLinear
  CurrentSpaces CurrentVectorSpaces CurrentCoefficientNorms CurrentDiracDensity
  SmoothFunctionSpaceUP CurrentSmoothLebesgue CurrentDensityAction
  EuclideanLebesgueDimensions SmoothingKernelUP SmoothingDilationUP
  SmoothingReflectedWeight CurrentKernelAverageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentKernelAverageExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Vector:=(exterior_power X 0%N).
Local Notation VN:=(@current_vector_mass R h2 n 0%N).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n 0%N).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull 0%N).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull 0%N).
Local Notation hV:=(@current_vector_smooth_space_laws R h2 n Full hFull 0%N).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Local Notation C:=(@current_space R h2 n Full hFull 0%N).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation w:=(fun z:X=>family epsilon (-z)).

(** Source for [current_kernel_average_exists]: the reflected
    unit-kernel average in 4.1.18, p. 374, is
    represented by an actual original zero-current. The
    smooth density is chosen only inside this proof. *)
Theorem current_kernel_average_exists:
  exists S:C,@is_current_kernel_average R h2 n w S.
Proof.
have hSmooth:norm_class_all_orders hNX hVN Full (fun z=>w z*:unit).
  move=>k.
  exact:(@norm_class_scalar_product R X Vector NX VN hNX hVN Full w
    (fun _:X=>unit) k
    (@smoothing_reflected_weight_smooth R n phi family hPhi hFamily epsilon hEpsilon k)
    (@norm_class_constant R X Vector NX VN hNX hVN Full unit k hFull)).
have [xi hXi]:=smooth_function_evaluation_surjective hV hSmooth.
exists (@current_smooth_lebesgue_map R h2 n 0%N xi)=>omega.
have hAction:=@current_smooth_lebesgue_action R h2 n 0%N xi omega.
have hPair:(fun z=>pairing (vv xi z)
    (@current_test_value R h2 n Full hFull 0%N omega z))=
    (fun z=>w z*zero_form_value (@current_test_value R h2 n Full hFull 0%N omega z)).
  apply:funext=>z;rewrite (hXi z Logic.I).
  rewrite (linZ ((@pairing_bilinear R X R^o 0%N).1 _))
    current_scalar_multivector_unit_pairing.
  by [].
by rewrite hPair in hAction.
Qed.
End CurrentKernelAverageExistence.
