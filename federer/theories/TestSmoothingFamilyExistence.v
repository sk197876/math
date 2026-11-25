(** Federer (1969), 4.1.2, p. 347: the
    original smooth-space smoothing family restricts to
    the original test space. Compact support is
    proved before the existing opaque linear-subspace
    lift supplies the actual test operator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed SmoothFunctionSpaceUP SmoothTestSubspaces SmoothTestSpaces
  SmoothingKernelUP SmoothingDilationUP SmoothSmoothingFamilyUP SmoothSmoothingSupport TestSmoothingFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section TestSmoothingFamilyExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.

(** Source for [test_smoothing_operator_exists]: the original
    Phi_epsilon*f belongs to D whenever f does,
    Federer 4.1.2, p. 347, with its
    exact values after the original inclusion into E. *)
Theorem test_smoothing_operator_exists e (he:0<e):
  exists Q:Hom DT DT,forall f:DT,inc (Q f)= P e (inc f).
Proof.
have hImage (f:DT):smooth_compact_support_subspace hE (P e (inc f)).
  have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
  have [C [_ hC]]:=@smooth_smoothing_support_bound R n Y NY hNY E ev hE phi hPhi family hFamily P hP K e (ltW he).
  exists C; exact:(@hC e he (lexx _) (inc f) hK).
pose L:=hom_comp (P e) inc.
have hL f:smooth_compact_support_subspace hE (L f).
  exact:(hImage f).
pose Q:=@LinearSubspaceLift.map R DT DT E (smooth_compact_support_subspace hE)
  inc (smooth_test_space_laws hE) L hL.
exists Q=>f.
have hValue:=@LinearSubspaceLift.evaluation R DT DT E (smooth_compact_support_subspace hE)
  inc (smooth_test_space_laws hE) L hL f.
rewrite /L hom_compE in hValue; exact hValue.
Qed.

(** Source for [test_smoothing_family_exists]: the original
    positive-scale smoothing endomorphisms exist on D,
    Federer 4.1.2, p. 347. The
    independently specified inclusion law is proved. *)
Theorem test_smoothing_family_exists:
  exists Q:R->Hom DT DT,@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.
Proof.
have hFor e:exists Q:Hom DT DT,0<e ->forall f:DT,inc (Q f)= P e (inc f).
  case:(pselect (0<e))=>he.
  - have [Q hQ]:=@test_smoothing_operator_exists e he.
    exists Q; by move=>_.
  - exists 0; by move=>/he.
have [Q hQ]:=choice hFor.
exists Q; exact hQ.
Qed.
End TestSmoothingFamilyExistence.
