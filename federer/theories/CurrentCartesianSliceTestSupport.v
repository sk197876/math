(** Federer (1969), 4.1.8, p. 360: the actual
    slice tests have a common first-variable compact bound
    and vanish when the second point lies outside the
    projected input support. Consumers use only the sealed
    slice law and earlier support theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorHomogeneousProducts AlternatingForms AlternatingDual
  CurrentSpaces CurrentTestValueLaws CurrentVectorFormInterior SmoothCompactSet SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation CurrentCartesianDomain CurrentCartesianSliceTestSealed
  CurrentCartesianSliceSmoothUP CurrentCartesianSliceSmoothSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceTestSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EA := (@current_smooth_space R h2 m A hA i).
Local Notation va := (@current_smooth_value R h2 m A hA i).
Local Notation hEA := (@current_smooth_space_laws R h2 m A hA i).
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation inc := (smooth_test_inclusion hEA).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_slice_test_smooth_laws]: the
    actual test inclusion preserves the original slice values
    and bilinearity in Federer 4.1.8, p. 360. This supporting
    adapter exposes no implementation of the sealed test witness. *)
Lemma current_cartesian_slice_test_smooth_laws:
  @is_current_cartesian_slice_smooth R h2 m n A B hA hB i j
    (fun b hb eta phi=>inc (F b hb eta phi)).
Proof.
have hF:=@CartesianSliceTest.laws R h2 m n A B hA hB i j.
move=>b hb;split.
- have hBilinear:=(@hF b hb).1.
  split.
  + move=>phi c eta theta.
    exact:(eq_trans (congr1 inc ((hBilinear.1 phi) c eta theta))
      ((hom_linear inc) c (F b hb eta phi) (F b hb theta phi))).
  + move=>eta c phi psi.
    exact:(eq_trans (congr1 inc ((hBilinear.2 eta) c phi psi))
      ((hom_linear inc) c (F b hb eta phi) (F b hb eta psi))).
- move=>eta phi a ha;exact:((@hF b hb).2 eta phi a ha).
Qed.

(** Source for [current_cartesian_slice_test_fixed_support]: one
    first projection bounds every actual first-variable test
    from a fixed input support step, supporting the continuity
    argument for phi_S in Federer 4.1.8, p. 360. *)
Theorem current_cartesian_slice_test_fixed_support
    (K:smooth_compact_set hNZ AB) (KA:smooth_compact_set hNX A):
  smooth_compact_carrier KA=p @` smooth_compact_carrier K->
  forall phi:DC,
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
  forall b (hb:B b) eta,
    @smooth_function_support R X (A_m X R^o i) NX hNX A EA va
      (inc (F b hb eta phi)) `<=` smooth_compact_carrier KA.
Proof.
move=>hKA phi hPhi b hb eta.
exact:(@current_cartesian_slice_smooth_fixed_support R h2 m n i j A B hA hB
  (fun b hb eta phi=>inc (F b hb eta phi)) current_cartesian_slice_test_smooth_laws
  K KA hKA phi hPhi b hb eta).
Qed.

(** Source for [current_cartesian_slice_test_zero_off_second_projection]:
    the original slice vanishes off the second projection
    of its input support, supporting compact support of phi_S
    in Federer 4.1.8, p. 360. The assertion concerns the
    actual test, before any current is applied. *)
Theorem current_cartesian_slice_test_zero_off_second_projection
    (K:smooth_compact_set hNZ AB) (phi:DC):
  @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
  forall b (hb:B b),~(q @` smooth_compact_carrier K) b->
    forall eta,F b hb eta phi=0.
Proof.
move=>hK b hb hOutside eta.
have hF:=@CartesianSliceTest.laws R h2 m n A B hA hB i j.
have hOff:forall z,~smooth_compact_carrier K z->
    @current_test_value R h2 (m+n) AB hAB (i+j) phi z=0.
  exact:(smooth_function_compact_support_iff hEC K (smooth_test_inclusion hEC phi)).1 hK.
apply:(smooth_test_values_extensional hEA)=>a ha.
have hLast:q (@euclidean_block_join R m n (a,b))=b.
  change ((@euclidean_block_split R m n (@euclidean_block_join R m n (a,b))).2=b).
  by rewrite euclidean_block_joinK.
have hNotK:~smooth_compact_carrier K (@euclidean_block_join R m n (a,b)).
  move=>hKz;apply:hOutside;exists (@euclidean_block_join R m n (a,b));first exact:hKz.
  exact:hLast.
have hZero:=hOff _ hNotK.
have hValue:=(@hF b hb).2 eta phi a ha.
have hInterior:=@current_vector_form_interior_bilinear R Z j i.
have hTestZero:smooth_test_value hEA (0:DA) a=0:=
  @current_test_zero_value R h2 m i A hA a.
rewrite hTestZero.
by rewrite hZero linear0 (bil0r hInterior) linear0 in hValue.
Qed.
End CurrentCartesianSliceTestSupport.
