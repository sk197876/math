(** Federer (1969), 4.1.8, p. 360: the original
    smooth slice phi_S is an actual compact test on B.
    Smoothness and the second-projection support are proved first;
    the original test-space image law then supplies its representative. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading
  AlternatingForms AlternatingPairing CurrentSpaces SmoothFunctionSupport
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation LinearSubspaceRepresentationUP
  CurrentCartesianDomain CurrentCartesianCompactProjections CurrentCartesianSliceTestSealed
  CurrentCartesianSliceFieldExistence CurrentCartesianSliceFieldSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceOutputTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation DC := (@current_test_space R h2 (m+n) AB hAB (i+j)).
Local Notation hEC := (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)).
Local Notation EB := (@current_smooth_space R h2 n B hB j).
Local Notation vb := (@current_smooth_value R h2 n B hB j).
Local Notation hEB := (@current_smooth_space_laws R h2 n B hB j).
Local Notation DB := (@current_test_space R h2 n B hB j).
Local Notation F := (fun (b:R_n R n) (hb:B b)=>@CartesianSliceTest.value R h2 m n A B hA hB i j b hb).

(** Source for [current_cartesian_slice_output_test_exists]: the
    form phi_S defined by the original eta pairings belongs
    to D^j(B), Federer 4.1.8, p. 360. This is actual
    test-space existence for every current, with no integration
    representation premise and no assumed slice continuity. *)
Theorem current_cartesian_slice_output_test_exists (S:CA) (phi:DC):
  exists g:DB,forall b (hb:B b) eta,
    pairing eta (@current_test_value R h2 n B hB j g b)=
      @current_value R h2 m A hA i S (F b hb eta phi).
Proof.
have[g hg]:=@current_cartesian_slice_field_exists R h2 m n i j A B hA hB S phi.
have[K hK]:=smooth_test_support_bound hEC phi.
have[KA [KB [hKA hKB]]]:=@current_cartesian_compact_projections R m n A B hA hB K.
have hSupport:=@current_cartesian_slice_field_fixed_support R h2 m n i j A B hA hB
  S K KB phi g hKB hK hg.
have hMember:smooth_compact_support_subspace hEB g by exists KB.
have[output hOutput]:=@subspace_representation_full R EB DB
  (smooth_compact_support_subspace hEB) (smooth_test_inclusion hEB)
  (smooth_test_space_laws hEB) g hMember.
exists output=>b hb eta.
change (pairing eta (vb (smooth_test_inclusion hEB output) b)=
  @current_value R h2 m A hA i S (F b hb eta phi)).
rewrite hOutput;exact:(@hg b hb eta).
Qed.
End CurrentCartesianSliceOutputTest.
