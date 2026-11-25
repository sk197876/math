(** Federer (1969), 4.1.8, p. 360: every original
    ordered derivative of phi_S has one uniform scalar input
    estimate on a fixed support step. The base input order
    depends only on S, eta and that step; each derivative
    word raises it by exactly the length of the word. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentSpaces DistributionDirectionalDerivative
  DistributionIteratedDerivative CurrentCartesianDomain CurrentCartesianSliceSealed
  CurrentCartesianSliceDirectional CurrentCartesianSliceIterated CurrentCartesianSliceUniformValueBound
  TestIteratedSupportSeminorm CurrentCartesianSliceTestSealed AlternatingPairing
  SmoothCompactSet SmoothFunctionSupport SmoothTestSpaces SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceIteratedValueBound.
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

(** Source for [current_cartesian_slice_iterated_value_bound]: the
    original repeated scalar slice pairings are controlled by
    a same-support input seminorm, uniformly in the original
    parameter point and input test. This supports the higher
    seminorm continuity argument in Federer 4.1.8, p. 360.
    No integration representation or slice-continuity premise is added. *)
Theorem current_cartesian_slice_iterated_value_bound
    (S:@current_space R h2 m A hA i) (K:smooth_compact_set hNZ AB)
    (eta:exterior_power Y j):
  exists r:nat,forall s:seq Y,exists M0:R,0<=M0 /\forall phi:DC,
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
    forall b (hb:B b),
      `|pairing eta (@current_test_value R h2 n B hB j (IterB s (H S phi)) b)|<=
      M0*smooth_function_derivative_seminorm
        (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K (r+size s)%N
        (smooth_test_inclusion hEC phi).
Proof.
have[r [M [hM hBase]]]:=@current_cartesian_slice_uniform_value_bound R h2 m n i j A B hA hB S K eta.
exists r=>s.
have[C [hC hNu]]:=@test_iterated_derivative_seminorm_bound R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB hAB EC vc hEC (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K [seq Q v | v<-s] r.
exists (M*C);split;first exact:mulr_ge0 hM hC.
move=>phi hPhi b hb.
have hSupport:=@test_iterated_derivative_compact_support R Z (A_m Z R^o (i+j))
  NZ (@current_form_comass R h2 (m+n) (i+j)) hNZ (@current_form_comass_real_norm R h2 (m+n) (i+j))
  AB hAB EC vc hEC (@current_smooth_derivatives R h2 (m+n) AB hAB (i+j))
  (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)) K [seq Q v | v<-s] phi hPhi.
have hFirst:=@hBase (IterC [seq Q v | v<-s] phi) hSupport b hb.
have hFinal:=le_trans hFirst (ler_wpM2l hM (hNu phi)).
rewrite mulrA size_map in hFinal.
rewrite (@current_cartesian_slice_iterated_commutation R h2 m n i j A B hA hB S phi s)
  (@CartesianSlice.laws R h2 m n i j A B hA hB S (IterC [seq Q v | v<-s] phi) b hb eta).
exact:hFinal.
Qed.
End CurrentCartesianSliceIteratedValueBound.
