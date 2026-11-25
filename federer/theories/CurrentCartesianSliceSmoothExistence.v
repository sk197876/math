(** Federer (1969), 4.1.8, p. 360: the original
    first-variable slice is an actual smooth form on A.
    The proof uses the original constant vector, right interior
    and pullback under a to (a,b). Compact support and
    smooth parameter dependence remain separate obligations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear BilinearPrecompose RealNormUP
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentSpaces CurrentVectorSpaces CurrentVectorFormInterior
  CurrentDegreeTransport SmoothTestSpaces SmoothConstantSealed SmoothFormPullbackUP
  SmoothFormPullbackSealed SmoothCurrentVectorInterior SmoothCurrentVectorInteriorBilinear
  CurrentCartesianDomain CurrentCartesianAffineSlice CurrentCartesianSliceSmoothUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSliceSmoothExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EA := (fun k=>@current_smooth_space R h2 m A hA k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation hEC := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation VC := (@current_vector_smooth_space R h2 (m+n) AB hAB j).
Local Notation vvc := (@current_vector_smooth_value R h2 (m+n) AB hAB j).
Local Notation hVC := (@current_vector_smooth_space_laws R h2 (m+n) AB hAB j).
Local Notation MV := (exterior_power Z j).
Local Notation MN := (@current_vector_mass R h2 (m+n) j).
Local Notation hMN := (@current_vector_mass_real_norm R h2 (m+n) j).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).
Local Notation M := (@smooth_current_vector_interior R h2 (m+n) j i AB hAB).

(** Source for [current_cartesian_slice_smooth_exists]: existence
    of the actual smooth first-variable form in the defining
    equation of Federer 4.1.8, p. 360. All selected objects
    occur inside this proof; no compact support or smooth
    dependence on the parameter is assumed. *)
Theorem current_cartesian_slice_smooth_exists:
  exists G:forall b:Y,B b->exterior_power Y j->DC (i+j)->EA i,
    @is_current_cartesian_slice_smooth R h2 m n A B hA hB i j G.
Proof.
pose C0:=@SmoothConstant.operator R Z MV NZ MN hNZ hMN AB hAB VC vvc hVC.
have hC0:=@SmoothConstant.laws R Z MV NZ MN hNZ hMN AB hAB VC vvc hVC.
pose C:=hom_comp C0 (hom_of_linear (exterior_power_map (hom_as_linear Q) j)).
pose I:=hom_comp (smooth_test_inclusion (hEC (j+i)))
  (@current_test_degree_transport R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j)).
pose fb:=fun (b:Y)(a:X)=>@euclidean_block_join R m n (a,b).
have hImage b (hb:B b):forall a,A a->AB (fb b a).
  exact:(@current_cartesian_affine_slice_image R m n A B b hb).
have hSmooth b:=@current_cartesian_affine_slice_smooth R m n A hA b.
pose pull:=fun (b:Y)(hb:B b)=>@SmoothFormPullback.operator R h2 m (m+n) i
  A AB hA hAB (fb b) (@hImage b hb) (@hSmooth b).
pose G:=fun (b:Y)(hb:B b) eta phi=>pull b hb (M (C eta) (I phi)).
have hPre:bilinear (fun eta phi=>M (C eta) (I phi)).
  exact:(@bilinear_linear_precompose R (exterior_power Y j) (DC (i+j)) VC (EC (j+i)) (EC i)
    (fun xi phi=>M xi phi)
    (@smooth_current_vector_interior_bilinear R h2 (m+n) j i AB hAB)
    (hom_as_linear C) (hom_as_linear I)).
exists G=>b hb;split.
- split.
  + move=>phi c eta theta.
    exact:(eq_trans (congr1 (pull b hb) ((hPre.1 phi) c eta theta))
      ((hom_linear (pull b hb)) c (M (C eta) (I phi)) (M (C theta) (I phi)))).
  + move=>eta c phi psi.
    exact:(eq_trans (congr1 (pull b hb) ((hPre.2 eta) c phi psi))
      ((hom_linear (pull b hb)) c (M (C eta) (I phi)) (M (C eta) (I psi)))).
- move=>eta phi a ha.
  have hPull:=@SmoothFormPullback.laws R h2 m (m+n) i A AB hA hAB
    (fb b) (@hImage b hb) (@hSmooth b).
  have hDifferential:=@current_cartesian_affine_slice_differential R m n A hA b a ha.
  have hPB:=@smooth_form_pullback_values R m (m+n) i A AB (EC i) (EA i)
    (vc i) (@current_smooth_value R h2 m A hA i) (fb b) (pull b hb) hPull
    (M (C eta) (I phi)) a P ha hDifferential.
  have hABab:AB (fb b a):=@hImage b hb a ha.
  have hInterior:=@smooth_current_vector_interior_values R h2 (m+n) j i AB hAB
    (C eta) (I phi) (fb b a) hABab.
  have hConstant:vvc (C eta) (fb b a)=exterior_power_map (hom_as_linear Q) j eta.
    change (vvc (C0 (exterior_power_map (hom_as_linear Q) j eta)) (fb b a)=
      exterior_power_map (hom_as_linear Q) j eta).
    exact:(@hC0 (exterior_power_map (hom_as_linear Q) j eta) (fb b a) hABab).
  have hInput:vc (j+i) (I phi) (fb b a)=form_reindex (addnC i j)
      (@current_test_value R h2 (m+n) AB hAB (i+j) phi (fb b a)).
    change (@current_test_value R h2 (m+n) AB hAB (j+i)
      (@current_test_degree_transport R h2 (m+n) AB hAB (i+j) (j+i) (addnC i j) phi)
      (fb b a)=form_reindex (addnC i j)
        (@current_test_value R h2 (m+n) AB hAB (i+j) phi (fb b a))).
    exact:current_test_degree_transport_values.
  rewrite hConstant hInput in hInterior.
  by rewrite /G hPB hInterior.
Qed.
End CurrentCartesianSliceSmoothExistence.
