(** Federer (1969), 4.1.8, p. 362: the
    actual point-inclusion pullback of every original
    separated mixed test. The values follow from the
    actual affine differential Q and the original
    block covector identities; no current identity
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  AlternatingForms AlternatingZero AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentCoefficientNorms CurrentSpaces CurrentDegreeTransport CurrentCartesianDomain
  CurrentCartesianPointInclusion CovectorCartesianPointInclusion CurrentCartesianTestProductSealed
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianPointPullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variable z:X.
Hypothesis hz:A z.
Local Notation f := (@current_cartesian_point_inclusion R m n z).
Local Notation Image := (fun y hy=>@current_cartesian_point_inclusion_image R m n A B z hz y hy).
Local Notation hSmooth := (@current_cartesian_point_inclusion_smooth R m n B hB z).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).
Local Notation EB := (fun d=>@current_smooth_space R h2 n B hB d).
Local Notation EC := (fun d=>@current_smooth_space R h2 (m+n) AB hAB d).
Local Notation vb := (fun d=>@current_smooth_value R h2 n B hB d).
Local Notation vc := (fun d=>@current_smooth_value R h2 (m+n) AB hAB d).
Local Notation hEC := (fun d=>@current_smooth_space_laws R h2 (m+n) AB hAB d).
Local Notation IC := (fun d=>smooth_test_inclusion (hEC d)).
Local Notation va := (fun d=>@current_test_value R h2 m A hA d).
Local Notation tb := (fun d=>@current_test_value R h2 n B hB d).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 n (m+n) d B AB hB hAB f Image hSmooth).

(** Source for [current_cartesian_point_pullback_values]: the
    actual pullback has the original Q-pullback values
    on every separated mixed test, supporting the
    identity phi_delta_z=epsilon_z#phi in Federer
    4.1.8, p. 362. Equal total degrees alone
    are identified. *)
Theorem current_cartesian_point_pullback_values d k l (e:(k+l)%N=d)
    (alpha:@current_test_space R h2 m A hA k)
    (beta:@current_test_space R h2 n B hB l) y (hy:B y):
  vb d (pull d (IC d (Tr _ _ e (Pure k l alpha beta)))) y=
    A_m_dual Q (form_reindex e (form_wedge h2 (scalar_bilinear R)
      (A_m_dual p (va k alpha z)) (A_m_dual q (tb l beta y)))).
Proof.
have hPull:=@smooth_form_pullback_values R n (m+n) d B AB
  (EC d) (EB d) (vc d) (vb d) f (pull d)
  (@SmoothFormPullback.laws R h2 n (m+n) d B AB hB hAB f Image hSmooth)
  (IC d (Tr _ _ e (Pure k l alpha beta))) y (@euclidean_last_injection_map R m n) hy
  (@current_cartesian_point_inclusion_differential R m n B hB z y hy).
have hTransport:=@current_test_degree_transport_values R h2 (m+n) AB hAB (k+l) d e
  (Pure k l alpha beta) (f y).
have hPure:=(@CartesianTestProduct.laws R h2 m n A B hA hB k l).2 alpha beta (f y) (Image y hy).
have hFirst:@euclidean_first_block_map R m n (f y)=z.
  change ((euclidean_block_split (euclidean_block_join (z,y))).1=z).
  by rewrite euclidean_block_joinK.
have hLast:@euclidean_last_block_map R m n (f y)=y.
  exact:current_cartesian_point_inclusion_left_inverse.
rewrite hPure hFirst hLast in hTransport.
exact:(eq_trans hPull (congr1 (fun a:A_m Z R^o d=>A_m_dual Q a) hTransport)).
Qed.

(** Source for [current_cartesian_point_pullback_diagonal]: the
    original diagonal pullback is alpha(z) beta,
    supporting delta_z times T=epsilon_z#T in
    Federer 4.1.8, p. 362. *)
Theorem current_cartesian_point_pullback_diagonal j
    (alpha:@current_test_space R h2 m A hA 0%N)
    (beta:@current_test_space R h2 n B hB j) y (hy:B y):
  vb j (pull j (IC j (Tr _ _ (add0n j) (Pure 0%N j alpha beta)))) y=
    zero_form_value (va 0%N alpha z)*:tb j beta y.
Proof.
have h:=@current_cartesian_point_pullback_values j 0%N j (add0n j) alpha beta y hy.
by rewrite current_point_covector_diagonal in h.
Qed.

(** Source for [current_cartesian_point_pullback_off_diagonal]:
    every original separated test of positive first
    degree has zero point-inclusion pullback, supporting
    Federer 4.1.8, p. 362. *)
Theorem current_cartesian_point_pullback_off_diagonal d k l (e:(k+l)%N=d)
    (alpha:@current_test_space R h2 m A hA k)
    (beta:@current_test_space R h2 n B hB l):k<>0%N->
  forall y,B y->vb d (pull d (IC d (Tr _ _ e (Pure k l alpha beta)))) y=0.
Proof.
move=>hk y hy.
have h:=@current_cartesian_point_pullback_values d k l e alpha beta y hy.
by rewrite (@current_point_covector_off_diagonal R h2 m n d k l e
  (va k alpha z) (tb l beta y) hk) in h.
Qed.
End CurrentCartesianPointPullback.
