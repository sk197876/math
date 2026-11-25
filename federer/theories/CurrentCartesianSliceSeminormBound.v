(** Federer (1969), 4.1.8, p. 360: one
    finite-order input seminorm controls every original output
    seminorm of a prescribed order. Finitely many already
    proved jet bounds and the original least-seminorm law
    supply the estimate, without enlarging the input support. *)
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
  FiniteExteriorPowers FiniteCoordinates CovectorProducts EuclideanCoordinateForms
  CurrentCartesianSliceJetBound SmoothDerivativeSeminormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceSeminormBound.
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


(** Source for [current_cartesian_slice_seminorm_bound]: the
    original phi to phi_S satisfies the fixed-step
    derivative-seminorm estimates used for its continuity in
    Federer 4.1.8, p. 360. The output compact
    index is arbitrary; the input order and constant
    are uniform over all inputs in the original K. *)
Theorem current_cartesian_slice_seminorm_bound
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB) p:
  exists r:nat,exists M0:R,0<=M0 /\forall L:smooth_compact_set hNY B,forall phi:DC,
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
    smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 n B hB j) L p
      (smooth_test_inclusion hEB (H S phi))<=
      M0*smooth_function_derivative_seminorm
        (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
        (smooth_test_inclusion hEC phi).
Proof.
pose admissible (phi:DC):Prop:=@smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ
  AB EC vc (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K.
pose q (a:'I_p.+1) (phi:DC) (b:Y):R:=
  @JN a (@DBjet a b (smooth_test_inclusion hEB (H S phi))).
have hBounds:forall a:'I_p.+1,exists r:nat,exists C:R,0<=C /\forall phi:DC,admissible phi->
    forall b:Y,B b->q a phi b<=C*smooth_function_derivative_seminorm
      (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r
      (smooth_test_inclusion hEC phi).
  move=>a;exact:(@current_cartesian_slice_jet_bound R h2 m n i j A B hA hB S K a).
have[r [M [hM hCommon]]]:=@finite_smooth_seminorm_control R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB EC vc (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K DC Y
  (smooth_test_inclusion hEC) admissible B (Finite.clone 'I_p.+1 _) q hBounds.
exists r,M;split;first exact:hM.
move=>L phi hPhi.
apply:(smooth_derivative_seminorm_least
  (smooth_function_derivative_seminorm_laws (@current_smooth_derivative_laws R h2 n B hB j) L p)).
- exact:(mulr_ge0 hM (smooth_derivative_seminorm_nonnegative
    (smooth_function_derivative_seminorm_laws
      (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K r)
    (smooth_test_inclusion hEC phi))).
- move=>ell hEll b hLb.
  have hIndex:(ell<p.+1)%N by rewrite ltnS.
  pose a:'I_p.+1:=Ordinal hIndex.
  exact:(@hCommon a phi hPhi b (smooth_compact_in_domain L b hLb)).
Qed.
End CurrentCartesianSliceSeminormBound.
