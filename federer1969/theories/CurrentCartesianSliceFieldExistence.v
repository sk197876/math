(** Federer (1969), 4.1.8, p. 360: the displayed
    eta pairings determine an actual smooth j-form phi_S
    on B. The original finite covector coordinates turn
    the separately proved scalar smoothness into field smoothness.
    Choices occur only inside this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentCoefficientNorms CurrentSpaces SmoothFunctionSpaceUP CurrentCartesianDomain
  CurrentCartesianSliceTestUP CurrentCartesianSliceTestUnique CurrentCartesianSliceTestSealed
  CurrentCartesianSlicePoint CurrentCartesianSliceScalarSmooth CurrentFormPairingSmoothness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceFieldExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation FB := (A_m Y R^o j).
Local Notation FN := (@current_form_comass R h2 n j).
Local Notation hFN := (@current_form_comass_real_norm R h2 n j).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [current_cartesian_slice_field_exists]: the original
    scalar equations for phi_S in Federer 4.1.8, p. 360,
    have a genuine smooth covector-field solution for every current S.
    Compact support and continuity of the resulting operator are
    proved separately; neither is an assumption of this theorem. *)
Theorem current_cartesian_slice_field_exists (S:CA) (phi:DC):
  exists g:EB,forall b (hb:B b) eta,
    pairing eta (vb g b)=@current_value R h2 m A hA i S (F b hb eta phi).
Proof.
have hF:=@CartesianSliceTest.laws R h2 m n A B hA hB i j.
have hPoint:forall b:Y,exists theta:FB,forall hb:B b,forall eta,
    pairing eta theta=@current_value R h2 m A hA i S (F b hb eta phi).
  move=>b;case:(pselect (B b))=>[hb|hNot].
  - have[theta hTheta]:=@current_cartesian_slice_point_exists R h2 m n i j A B hA hB S phi b hb.
    exists theta=>hb' eta.
    have hMember:=@current_cartesian_slice_test_membership_independent R h2 m n A B hA hB
      i j F hF b hb hb' eta phi.
    exact:(eq_trans (hTheta eta) (congr1 (@current_value R h2 m A hA i S) hMember)).
  - exists 0=>hb;exact:(False_ind _ (hNot hb)).
have[g hg]:=choice hPoint.
have hSmooth:norm_class_all_orders hNY hFN B g.
  apply:(@current_form_field_smooth_from_pairings R h2 Y NY hNY n j B hB g)=>eta.
  have[h [hSmooth hValues]]:=@current_cartesian_slice_scalar_smooth R h2 m n i j A B hA hB
    S phi eta.
  move=>k.
  apply:(@norm_class_domain_agreement R Y R^o NY (fun t:R^o=>`|t|) hNY
    (@scalar_absolute_value_norm R) B h (fun b=>pairing eta (g b)) k _ (hSmooth k))=>b hb.
  exact:(eq_trans (@hValues b hb) (esym (@hg b hb eta))).
have[output hOutput]:=@smooth_function_evaluation_surjective R Y FB NY FN hNY hFN
  B EB vb hEB g hSmooth.
exists output=>b hb eta.
rewrite (@hOutput b hb);exact:(@hg b hb eta).
Qed.
End CurrentCartesianSliceFieldExistence.
