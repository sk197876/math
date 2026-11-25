(** Federer (1969), 4.1.8, p. 360: the original
    slice field phi_S is supported in the second projection
    of the compact input support. This supporting theorem uses
    actual pointwise covector separation and the already proved
    zero first-variable test, without a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading AlternatingForms AlternatingPairing CurrentCoefficientNorms CurrentSpaces SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces CurrentCartesianDomain
  CurrentCartesianSliceTestSealed CurrentCartesianSliceTestSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceFieldSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [current_cartesian_slice_field_fixed_support]: one
    second-projection compact set supports every original phi_S
    from a fixed input support step, supporting Federer 4.1.8,
    p. 360. The conclusion concerns the genuine smooth form
    space on B, with its original zero representative outside B. *)
Theorem current_cartesian_slice_field_fixed_support (S:CA)
    (K:smooth_compact_set hNZ AB) (KB:smooth_compact_set hNY B)
    (phi:DC) (g:EB):
  smooth_compact_carrier KB=q @` smooth_compact_carrier K->
  @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
    (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
  (forall b (hb:B b) eta,pairing eta (vb g b)=
    @current_value R h2 m A hA i S (F b hb eta phi))->
  @smooth_function_support R Y (A_m Y R^o j) NY hNY B EB vb g
    `<=` smooth_compact_carrier KB.
Proof.
move=>hKB hPhi hValues.
apply:(smooth_function_compact_support_iff hEB KB g).2=>b hOutside.
case:(pselect (B b))=>[hb|hNot].
- have hNotProjection:~(q @` smooth_compact_carrier K) b by rewrite -hKB.
  apply:pairing_ext=>eta.
  have hZero:=@current_cartesian_slice_test_zero_off_second_projection R h2 m n i j
    A B hA hB K phi hPhi b hb hNotProjection eta.
  have hPairZero:pairing eta (0:A_m Y R^o j)=0.
    exact:(bil0r (@pairing_bilinear R Y R^o j) eta).
  have hScalarZero:@current_value R h2 m A hA i S 0=0 by rewrite linear0.
  exact:(eq_trans (@hValues b hb eta)
    (eq_trans (congr1 (@current_value R h2 m A hA i S) hZero)
      (eq_trans hScalarZero (esym hPairZero)))).
- exact:(@smooth_function_evaluation_outside R Y (A_m Y R^o j) NY
    (@current_form_comass R h2 n j) hNY
    (@current_form_comass_real_norm R h2 n j) B EB vb hEB g b hNot).
Qed.
End CurrentCartesianSliceFieldSupport.
