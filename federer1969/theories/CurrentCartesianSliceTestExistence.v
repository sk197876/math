(** Federer (1969), 4.1.8, p. 360: the first-variable
    slice is an actual compact test before S acts on it.
    Existence follows from the proved smooth slice and its
    compact support. The subspace lift is opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading CurrentSpaces SmoothTestSubspaces SmoothTestSpaces
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed CurrentCartesianDomain
  CurrentCartesianSliceTestUP CurrentCartesianSliceSmoothUP
  CurrentCartesianSliceSmoothExistence CurrentCartesianSliceSmoothSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSliceTestExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EA := (@current_smooth_space R h2 m A hA i).
Local Notation va := (@current_smooth_value R h2 m A hA i).
Local Notation hEA := (@current_smooth_space_laws R h2 m A hA i).
Local Notation DA := (@current_test_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).

(** Source for [current_cartesian_slice_test_exists]: the
    first-variable form displayed in the definition of phi_S
    belongs to the original test space, Federer 4.1.8,
    p. 360. The theorem proves its bilinearity and values;
    it assumes no slice or product-current existence. *)
Theorem current_cartesian_slice_test_exists:
  exists F:forall b:Y,B b->exterior_power Y j->DC->DA,
    @is_current_cartesian_slice_test R h2 m n A B hA hB i j F.
Proof.
have[G hG]:=@current_cartesian_slice_smooth_exists R h2 m n i j A B hA hB.
pose S:=smooth_compact_support_subspace hEA.
pose inc:=smooth_test_inclusion hEA.
pose hInc:=smooth_test_space_laws hEA.
have hMember b (hb:B b) eta phi:S (G b hb eta phi).
  exact:(@current_cartesian_slice_smooth_compact_support R h2 m n i j A B hA hB
    G hG b hb eta phi).
pose L:=fun (b:Y)(hb:B b)(eta:exterior_power Y j)=>
  @HomMap R DC EA (fun phi=>G b hb eta phi)
    (introT (asboolP _) (((@hG b hb).1).2 eta)).
pose lift:=fun (b:Y)(hb:B b)(eta:exterior_power Y j)=>
  @LinearSubspaceLift.map R DC DA EA S inc hInc (L b hb eta) (@hMember b hb eta).
pose F:=fun (b:Y)(hb:B b)(eta:exterior_power Y j)(phi:DC)=>lift b hb eta phi.
have hIncluded b (hb:B b) eta phi:inc (F b hb eta phi)=G b hb eta phi.
  exact:(@LinearSubspaceLift.evaluation R DC DA EA S inc hInc
    (L b hb eta) (@hMember b hb eta) phi).
exists F=>b hb;split.
- split.
  + move=>phi c eta theta.
    apply:(subspace_representation_injective hInc).
    have hLinear:=(((@hG b hb).1).1 phi) c eta theta.
    have hBack:=congr2 (fun U V:EA=>c*:U+V)
      (esym (@hIncluded b hb eta phi)) (esym (@hIncluded b hb theta phi)).
    have hIncLinear:inc (c*:F b hb eta phi+F b hb theta phi)=
        c*:inc (F b hb eta phi)+inc (F b hb theta phi).
      exact:linearP.
    exact:(eq_trans (@hIncluded b hb (c*:eta+theta) phi)
      (eq_trans hLinear (eq_trans hBack (esym hIncLinear)))).
  + move=>eta;exact:(hom_linear (lift b hb eta)).
- move=>eta phi a ha.
  have hEvaluation:=congr1 (fun psi:EA=>va psi a) (@hIncluded b hb eta phi).
  exact:(eq_trans hEvaluation ((@hG b hb).2 eta phi a ha)).
Qed.
End CurrentCartesianSliceTestExistence.
