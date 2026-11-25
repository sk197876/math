(** Federer (1969), 4.1.8, p. 360: the original
    slice phi to phi_S is an actual linear operator
    between the genuine test spaces. Its displayed pairings
    prove linearity; all choices remain in the existence proof.
    Continuity for the literal final topologies is a separate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing CurrentSpaces
  CurrentTestValueLaws SmoothTestEvaluation CurrentCartesianDomain CurrentCartesianSliceUP
  CurrentCartesianSliceTestSealed CurrentCartesianSliceOutputTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSliceExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation vb := (@current_test_value R h2 n B hB j).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [current_cartesian_slice_exists]: the displayed
    original phi_S of Federer 4.1.8, p. 360, defines
    a linear operator on every original test. No continuity,
    product-current existence or mixed-test density conclusion is
    included among the hypotheses of this existence statement. *)
Theorem current_cartesian_slice_exists (S:CA):
  exists H:Hom DC DB,@is_current_cartesian_slice R h2 m n i j A B hA hB S H.
Proof.
have hPoint:forall phi:DC,exists g:DB,forall b (hb:B b) eta,
    pairing eta (vb g b)=@current_value R h2 m A hA i S (F b hb eta phi).
  move=>phi;exact:(@current_cartesian_slice_output_test_exists R h2 m n i j A B hA hB S phi).
have[G hG]:=choice hPoint.
have hF:=@CartesianSliceTest.laws R h2 m n A B hA hB i j.
have hLinear:forall c phi psi,G (c*:phi+psi)=c*:G phi+G psi.
  move=>c phi psi;apply:(smooth_test_values_extensional hEB)=>b hb.
  apply:pairing_ext=>eta.
  change (pairing eta (vb (G (c*:phi+psi)) b)=pairing eta (vb (c*:G phi+G psi) b)).
  have hSlice:=(((@hF b hb).1).2 eta) c phi psi.
  have hPair:=(@pairing_bilinear R (R_n R n) R^o j).2 eta c (vb (G phi) b) (vb (G psi) b).
  rewrite (@current_test_add_value R h2 n j B hB (c*:G phi) (G psi) b)
    (@current_test_scale_value R h2 n j B hB c (G phi) b) hPair.
  rewrite (@hG (c*:phi+psi) b hb eta) hSlice (hom_linear (@current_value R h2 m A hA i S))
    (@hG phi b hb eta) (@hG psi b hb eta).
  reflexivity.
exists (@HomMap R DC DB G (introT (asboolP _) hLinear))=>phi b hb eta.
exact:(@hG phi b hb eta).
Qed.
End CurrentCartesianSliceExistence.
