(** Federer (1969), 4.1.8, p. 360:
    every pair of factor support points belongs to
    the support of the original product. Use the original
    local nonzero tests and the already proved product-ball
    neighbourhood theorem, without a measure representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentTestValueLaws CurrentSupportGeometry SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentCartesianDomain
  CurrentCartesianCompactProjections CurrentCartesianSliceTestSealed CurrentCartesianSliceTestSupport
  CurrentCartesianSliceFieldSupport CurrentCartesianSliceSealed CurrentCartesianProductSealed
  CurrentCartesianProductAction FunctionalSupportUP CurrentCartesianOpenCylinders
  CurrentCartesianProductAnnihilation CurrentSupportLocalTest CurrentCartesianSupportRectangle
  CurrentCartesianTestProductSealed CurrentCartesianTestProductSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import Order.TTheory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianSupportLower.
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
Local Notation EC := (@current_smooth_space R h2 (m+n) AB hAB (i+j)).
Local Notation vc := (@current_smooth_value R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation hDC := (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j)).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation hDB := (@current_smooth_derivative_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation H := (fun S=>@CartesianSlice.value R h2 m n i j A B hA hB S).

Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation X := (R_n R m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB j).
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation ea := (@current_value R h2 m A hA i).
Local Notation eb := (@current_value R h2 n B hB j).
Local Notation ec := (@current_value R h2 (m+n) AB hAB (i+j)).
Local Notation supportA := (@current_test_support R h2 m i A hA).
Local Notation supportB := (@current_test_support R h2 n j B hB).
Local Notation supportC := (@current_test_support R h2 (m+n) (i+j) AB hAB).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation F := (fun (b:Y) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
(** Source for [current_cartesian_support_lower]: every pair
    of original factor support points belongs to the support
    of the actual product current, one direction of the
    exact identity in Federer 4.1.8, p. 360.
    The original separated-test action detects every product
    neighbourhood, including zero-dimensional coordinate blocks. *)
Theorem current_cartesian_support_lower (S:CA) (T:CB):
  @euclidean_cartesian_set R m n
    (@current_support R h2 m A hA i S) (@current_support R h2 n B hB j T) `<=`
  @current_support R h2 (m+n) AB hAB (i+j) (Product S T).
Proof.
move=>z [hS hT].
have hDomain:AB z:=conj hS.1 hT.1.
split;first exact:hDomain.
move=>[W [hAnn hWz]].
have[U [V [hU [hV [hUa [hVb [hUA [hVB hRect]]]]]]]]:=
  @current_cartesian_support_rectangle R m n A B hA hB z W hDomain hAnn.1 hWz.
have[a [ha hActionA]]:=@current_support_local_nonzero_test R h2 m i A hA S (p z) U hS hU hUa.
have[b [hb hActionB]]:=@current_support_local_nonzero_test R h2 n j B hB T (q z) V hT hV hVb.
have hTestSupport:supportC (Pure i j a b) `<=` W.
  move=>x hx;apply:hRect.
  have hProductSupport:=@current_cartesian_test_product_support R h2 m n A B hA hB i j a b x hx.
  split.
  - exact:(ha (p x) hProductSupport.1).
  - exact:(hb (q x) hProductSupport.2).
have hAction:=hAnn.2 (Pure i j a b) hTestSupport.
rewrite ((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).1 a b) in hAction.
move/eqP:hAction;rewrite mulf_eq0=>/orP [/eqP hZeroA|/eqP hZeroB].
- exact:hActionA hZeroA.
- exact:hActionB hZeroB.
Qed.
End CurrentCartesianSupportLower.
