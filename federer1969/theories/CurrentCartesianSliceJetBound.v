(** Federer (1969), 4.1.8, p. 360: every actual
    higher differential of the original slice has a uniform
    finite-order bound on the input support step. The proof
    combines the original finite covector expansion and multiindex
    differential reconstruction with the proved repeated slice bounds.
    No continuity of the slice operator is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentSpaces DistributionDirectionalDerivative
  DistributionIteratedDerivative CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceDirectional CurrentCartesianSliceIterated CurrentCartesianSliceUniformValueBound
  TestIteratedSupportSeminorm CurrentCartesianSliceTestSealed AlternatingPairing
  SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothFunctionTopology
  CurrentCartesianSliceIteratedValueBound CurrentFormCoordinateNormBound CurrentTestJetReconstruction
  FiniteSmoothSeminormControl ContinuousMultilinearSealed ContinuousMultilinearNorm
  SymmetricMultiIndices SymmetricMonomials SymmetricMonomialTuples ExteriorIndices
  FiniteExteriorPowers FiniteCoordinates CovectorProducts EuclideanCoordinateForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceJetBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation IterC := (@distribution_test_iterated_derivative R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB hAB EC vc hEC (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j))).
Local Notation IterB := (@distribution_test_iterated_derivative R Y (A_m Y R^o j)
  NY (@current_form_comass R h2 n j) hNY (@current_form_comass_real_norm R h2 n j)
  B hB EB vb hEB (@current_smooth_derivatives R h2 n B hB j)
  (@current_smooth_derivative_laws R h2 n B hB j)).

Local Notation F := (fun (b:Y) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

Local Notation FB := (A_m Y R^o j).
Local Notation NB := (@current_form_comass R h2 n j).
Local Notation hNB := (@current_form_comass_real_norm R h2 n j).
Local Notation J := (fun k=>@ContinuousMultilinear.space R k Y FB NY NB hNY hNB).
Local Notation JN := (fun k=>@ContinuousMultilinear.norm R k Y FB NY NB hNY hNB).
Local Notation hJ := (fun k=>@ContinuousMultilinear.laws R k Y FB NY NB hNY hNB).
Local Notation DBjet := (@current_smooth_derivatives R h2 n B hB j).
Local Notation e := (fun lambda:Lambda n j=>e_lambda (@coordinate_basis R n) (val lambda)).
Local Notation omega := (@omega_lambda R h2 Y n (@euclidean_coordinate_form R n) j).

(** Source for [current_cartesian_slice_jet_bound]: one original
    input seminorm bounds an entire prescribed output derivative
    order, uniformly at every original point of B and
    every input in the same support step, supporting the
    continuity assertion in Federer 4.1.8, p. 360. *)
Theorem current_cartesian_slice_jet_bound
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB) k:
  exists r:nat,exists M0:R,0<=M0 /\forall phi:DC,
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
    forall b (hb:B b),@JN k (@DBjet k b (smooth_test_inclusion hEB (H S phi)))<=
      M0*smooth_function_derivative_seminorm
        (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
        (smooth_test_inclusion hEC phi).
Proof.
have[iota [hIota hReconstruct]]:=@current_test_jet_reconstruction R h2 n j B hB k.
pose I:finType:=Finite.clone (symmetric_indices n k * Lambda n j)%type _.
pose word (alpha:symmetric_indices n k):seq Y:=symmetric_monomial_tuple (@coordinate_basis R n) alpha.
pose admissible (phi:DC):Prop:=@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ
  AB EC vc (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K.
pose q (a:I) (phi:DC) (b:Y):R:=
  `|pairing (e a.2) (@current_test_value R h2 n B hB j (IterB (word a.1) (H S phi)) b)|.
have hBounds:forall a:I,exists r:nat,exists C:R,0<=C /\forall phi:DC,admissible phi->
    forall b:Y,B b->q a phi b<=C*smooth_function_derivative_seminorm
      (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
      (smooth_test_inclusion hEC phi).
  move=>a.
  have[r hOrders]:=@current_cartesian_slice_iterated_value_bound R h2 m n i j A B hA hB S K (e a.2).
  have[C [hC hBound]]:=hOrders (word a.1).
  exists (r+size (word a.1))%N,C;split;first exact:hC.
  move=>phi hPhi b hb;exact:(@hBound phi hPhi b hb).
have[r [M [hM hCommon]]]:=@finite_smooth_seminorm_control R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB EC vc (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K DC Y
  (smooth_test_inclusion hEC) admissible B I q hBounds.
have[coefficients hCoefficients]:=choice hIota.
pose weights:=\sum_(lambda:Lambda n j) NB (omega lambda).
pose coefficientSum:=\sum_(alpha:symmetric_indices n k) coefficients alpha.
have hWeights:0<=weights.
  apply:sumr_ge0=>lambda _;exact:(real_seminorm_nonnegative hNB.1 (omega lambda)).
have hCoefficientSum:0<=coefficientSum.
  apply:sumr_ge0=>alpha _;exact:(hCoefficients alpha).1.
exists r,(coefficientSum*M*weights);split.
- exact:(mulr_ge0 (mulr_ge0 hCoefficientSum hM) hWeights).
- move=>phi hPhi b hb.
  pose p:=smooth_function_derivative_seminorm
    (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
    (smooth_test_inclusion hEC phi).
  pose theta (alpha:symmetric_indices n k):FB:=
    @current_test_value R h2 n B hB j (IterB (word alpha) (H S phi)) b.
  have hPointNorm alpha:NB (theta alpha)<=(M * p)*weights.
    apply:le_trans (@current_form_coordinate_norm_bound R h2 n j (theta alpha)) _.
    rewrite /weights mulr_sumr.
    apply:ler_sum=>lambda _.
    exact:(ler_wpM2r (real_seminorm_nonnegative hNB.1 (omega lambda))
      (@hCommon (alpha,lambda) phi hPhi b hb)).
  have hTerm alpha:@JN k (iota alpha (theta alpha))<=
      coefficients alpha*((M * p)*weights).
    exact:(le_trans ((hCoefficients alpha).2 (theta alpha))
      (ler_wpM2l (hCoefficients alpha).1 (hPointNorm alpha))).
  have hSum:=@real_seminorm_sum R (J k) (@JN k)
    (continuous_multilinear_norm_is_norm hNB (hJ k)).1
    (Finite.clone (symmetric_indices n k) _) (fun alpha=>iota alpha (theta alpha)).
  rewrite -(@hReconstruct (H S phi) b hb) in hSum.
  have hFinite:(\sum_(alpha:symmetric_indices n k) @JN k (iota alpha (theta alpha)))<=
      \sum_(alpha:symmetric_indices n k) coefficients alpha*((M * p)*weights).
    apply:ler_sum=>alpha _;exact:hTerm.
  have hFinal:=le_trans hSum hFinite.
  rewrite -mulr_suml (mulrAC M p weights) !mulrA in hFinal.
  exact:hFinal.
Qed.
End CurrentCartesianSliceJetBound.
