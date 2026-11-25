(** Federer (1969), 4.1.8, p. 361: the original
    Cartesian interchange pulls a separated compact test
    back to its reversed product with the exact graded
    sign. This proves equality in the actual smooth
    space and retains every equal total degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwapLinear
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentTestValueLaws CurrentDegreeTransport SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentCartesianDomain CurrentCartesianSwapDomain CurrentCartesianTestProductSealed
  CovectorCartesianSwap FormReindexPullback CurrentCartesianSwapPurePullback
  CurrentCartesianProductSealed CurrentPushforwardSealed CurrentPushforwardUP
  NormMetric NormOpenTopology CurrentSupportGeometry CurrentCartesianSwapPushforward
  CurrentCartesianMixedExtensional CurrentCartesianProductTransportedAction
  CurrentPointEvaluation CurrentDegreeTransportComposition CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianProductSwap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BA := (@euclidean_cartesian_set R n m B A).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA := (@current_cartesian_domain_open R n m B A hB hA).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).
Local Notation Image := (fun z hz=>@current_cartesian_swap_image R m n A B z hz).
Local Notation hSmooth := (@euclidean_cartesian_swap_smooth R m n AB hAB).
Local Notation EA := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation EB := (fun k=>@current_smooth_space R h2 (n+m) BA hBA k).
Local Notation va := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation vb := (fun k=>@current_smooth_value R h2 (n+m) BA hBA k).
Local Notation hEA := (fun k=>@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation hEB := (fun k=>@current_smooth_space_laws R h2 (n+m) BA hBA k).
Local Notation IA := (fun k=>smooth_test_inclusion (hEA k)).
Local Notation IB := (fun k=>smooth_test_inclusion (hEB k)).
Local Notation PureA := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation PureB := (fun k l=>@CartesianTestProduct.value R h2 n m B A hB hA k l).
Local Notation TrA := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation TrB := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (n+m) BA hBA a b e).
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 (m+n) (n+m) d
  AB BA hAB hBA swap Image hSmooth).

Local Notation CA := (fun k=>@current_space R h2 m A hA k).
Local Notation CB := (fun k=>@current_space R h2 n B hB k).
Local Notation CC := (fun k=>@current_space R h2 (m+n) AB hAB k).
Local Notation CR := (fun k=>@current_space R h2 (n+m) BA hBA k).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Open Scope classical_set_scope.

Local Notation SwapC := (fun d C=>@current_cartesian_swap_current R h2 m n A B hA hB d C).
Local Notation ReverseProduct := (fun i j=>@CartesianCurrentProduct.value R h2 n m i j B A hB hA).
Local Notation CTrB := (fun a b (e:a=b)=>@current_degree_transport R h2 (n+m) BA hBA a b e).

(** Source for [current_cartesian_product_swap]: the original
    w#(S times T) equals (-1)^(ij) T times S,
    Federer 4.1.8, p. 361. The canonical degree
    identification and the original support-proper pushforward
    retain arbitrary factor currents and all zero degrees. *)
Theorem current_cartesian_product_swap i j (S:CA i) (T:CB j):
  CTrB _ _ (addnC i j) (SwapC (i+j) (Product i j S T))=
    (-1:R)^+(i * j)*:ReverseProduct j i T S.
Proof.
apply:(@current_cartesian_mixed_values_extensional R h2 n m B A hB hA (j+i)).
move=>k l e a b.
have hScale:
    @current_value R h2 (n+m) BA hBA (j+i)
      ((-1:R)^+(i * j)*:ReverseProduct j i T S) (TrB _ _ e (PureB k l a b))=
    (-1:R)^+(i * j)*@current_value R h2 (n+m) BA hBA (j+i)
      (ReverseProduct j i T S) (TrB _ _ e (PureB k l a b)).
  change (@current_point_evaluation R h2 (n+m) (j+i) BA hBA (TrB _ _ e (PureB k l a b))
    ((-1:R)^+(i * j)*:ReverseProduct j i T S)=
    (-1:R)^+(i * j)*:@current_point_evaluation R h2 (n+m) (j+i) BA hBA
      (TrB _ _ e (PureB k l a b)) (ReverseProduct j i T S)).
  exact:(linZ (hom_linear (@current_point_evaluation R h2 (n+m) (j+i) BA hBA
    (TrB _ _ e (PureB k l a b)))) ((-1:R)^+(i * j)) (ReverseProduct j i T S)).
cbn beta.
rewrite hScale (@current_degree_transport_evaluation R h2 (n+m) BA hBA (i+j) (j+i)
  (addnC i j) (SwapC (i+j) (Product i j S T)) (TrB _ _ e (PureB k l a b)))
  current_test_degree_transport_composition.
rewrite (@current_cartesian_swap_mixed_action R h2 m n A B hA hB i j S T k l
  (eq_trans e (esym (addnC i j))) a b).
case:(pselect (k = j))=>hk.
- subst k.
  have hl:l = i.
    apply/eqP;have heq:(j+l == j+i)%N:=introT eqP e.
    by rewrite eqn_add2l in heq.
  subst l.
  rewrite !current_test_degree_transport_identity
    ((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).1 b a)
    ((@CartesianCurrentProduct.laws R h2 n m j i B A hB hA T S).1 a b).
  by rewrite (mulnC j i) (mulrC
    (@current_value R h2 m A hA i S b) (@current_value R h2 n B hB j T a)).
- have hSource:=@current_cartesian_product_transported_off_second R h2 m n A B hA hB
    i j (i+j) (erefl (i+j)%N) S T l k
    (eq_trans (addnC l k) (eq_trans e (esym (addnC i j)))) hk b a.
  rewrite current_degree_transport_identity in hSource.
  have hTarget:=(@CartesianCurrentProduct.laws R h2 n m j i B A hB hA T S).2 k l e hk a b.
  by rewrite hSource hTarget !mulr0.
Qed.
End CurrentCartesianProductSwap.
