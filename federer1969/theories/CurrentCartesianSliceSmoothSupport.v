(** Federer (1969), 4.1.8, p. 360: the form to
    which S is applied is a genuine compact test on A.
    Its support lies in the first projection of the input
    support. This is proved from the original pointwise slice law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentSpaces CurrentVectorFormInterior SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianSliceSmoothUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSliceSmoothSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
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
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation p := (@euclidean_first_block_map R m n).

(** Source for [current_cartesian_slice_smooth_fixed_support]:
    one compact first projection bounds all first-variable
    slices of every input supported in K, supporting Federer
    4.1.8, p. 360. The bound is independent of b, eta
    and the input test within that original support step. *)
Theorem current_cartesian_slice_smooth_fixed_support
    (G:forall b:Y,B b->exterior_power Y j->DC->EA):
  @is_current_cartesian_slice_smooth R h2 m n A B hA hB i j G->
  forall (K:smooth_compact_set hNZ AB) (KA:smooth_compact_set hNX A),
    smooth_compact_carrier KA=p @` smooth_compact_carrier K->
  forall phi,
    @smooth_function_support R Z (A_m Z R^o (i+j)) NZ hNZ AB EC vc
      (smooth_test_inclusion hEC phi) `<=` smooth_compact_carrier K->
  forall b (hb:B b) eta,
    @smooth_function_support R X (A_m X R^o i) NX hNX A EA va
      (G b hb eta phi) `<=` smooth_compact_carrier KA.
Proof.
move=>hG K KA hKA phi hK b hb eta.
have hOff:forall z,~smooth_compact_carrier K z->
    @current_test_value R h2 (m+n) AB hAB (i+j) phi z=0.
  exact:(smooth_function_compact_support_iff hEC K (smooth_test_inclusion hEC phi)).1 hK.
apply:(smooth_function_compact_support_iff hEA KA _).2=>a hOutside.
case:(pselect (A a))=>ha;last exact:(smooth_function_evaluation_outside hEA (G b hb eta phi) ha).
have hFirst:p (@euclidean_block_join R m n (a,b))=a.
  change ((@euclidean_block_split R m n (@euclidean_block_join R m n (a,b))).1=a).
  by rewrite euclidean_block_joinK.
have hNotK:~smooth_compact_carrier K (@euclidean_block_join R m n (a,b)).
  move=>hKz;apply:hOutside;rewrite hKA.
  exists (@euclidean_block_join R m n (a,b));first exact:hKz.
  exact:hFirst.
have hZero:=hOff _ hNotK.
have hValue:=(@hG b hb).2 eta phi a ha.
have hInterior:=@current_vector_form_interior_bilinear R Z j i.
by rewrite hZero linear0 (bil0r hInterior) linear0 in hValue.
Qed.

(** Source for [current_cartesian_slice_smooth_compact_support]:
    compact support of the first-variable test in Federer
    4.1.8, p. 360. The conclusion follows from actual
    input support and the original slice formula; it is
    not an additional assumption on the slice family. *)
Theorem current_cartesian_slice_smooth_compact_support
    (G:forall b:Y,B b->exterior_power Y j->DC->EA):
  @is_current_cartesian_slice_smooth R h2 m n A B hA hB i j G->
  forall b (hb:B b) eta phi,exists KA:smooth_compact_set hNX A,
    @smooth_function_support R X (A_m X R^o i) NX hNX A EA va
      (G b hb eta phi) `<=` smooth_compact_carrier KA.
Proof.
move=>hG b hb eta phi.
have[K hK]:=smooth_test_support_bound hEC phi.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
exists KA;exact:(@current_cartesian_slice_smooth_fixed_support G hG K KA hKA phi hK b hb eta).
Qed.
End CurrentCartesianSliceSmoothSupport.
