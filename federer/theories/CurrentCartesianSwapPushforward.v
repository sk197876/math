(** Federer (1969), 4.1.8, p. 361: the original
    Cartesian interchange pulls a separated compact test
    back to its reversed product with the exact graded
    sign. This proves equality in the actual smooth
    space and retains every equal total degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwapLinear
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients ExteriorHomogeneousProducts
  CurrentSpaces SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation
  CurrentTestValueLaws CurrentDegreeTransport SmoothFormPullbackUP SmoothFormPullbackSealed
  CurrentCartesianDomain CurrentCartesianSwapDomain CurrentCartesianTestProductSealed
  CovectorCartesianSwap FormReindexPullback CurrentCartesianSwapPurePullback
  CurrentCartesianProductSealed CurrentPushforwardSealed CurrentPushforwardUP
  NormMetric NormOpenTopology NormBoundedLinearTopology CurrentSupportGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianSwapPushforward.
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

(** Source for [current_cartesian_swap_current]: the original
    w pushforward in Federer 4.1.8, p. 361,
    using the existing sealed pushforward and the proved
    properness of w on the actual current support. *)
Definition current_cartesian_swap_current d (C:CC d):CR d:=
  @CurrentPushforward.value R h2 (m+n) (n+m) d AB BA hAB hBA C swap Image hSmooth
    (@current_cartesian_swap_proper_on_support R h2 m n d A B hA hB C).

(** Source for [current_cartesian_swap_action]: every genuine
    compact source test agreeing with the original pulled-back
    target test gives the original swap pushforward value,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_swap_action d (C:CC d)
    (phi:@current_test_space R h2 (n+m) BA hBA d)
    (psi:@current_test_space R h2 (m+n) AB hAB d):
  (forall z,AB z->@current_test_value R h2 (m+n) AB hAB d psi z=
    va d (pull d (IB d phi)) z)->
  @current_value R h2 (n+m) BA hBA d (current_cartesian_swap_current C) phi=
    @current_value R h2 (m+n) AB hAB d C psi.
Proof.
move=>hPoint.
apply:(@CurrentPushforward.laws R h2 (m+n) (n+m) d AB BA hAB hBA C swap Image hSmooth
  (@current_cartesian_swap_proper_on_support R h2 m n d A B hA hB C) phi psi).
exists AB;split.
- rewrite openE=>z hz.
  exact:(@norm_domain_interior_neighbourhood R (R_n R (m+n))
    (inner_norm (@euclidean_inner_productP R (m+n)))
    (inner_norm_real_norm (@euclidean_inner_productP R (m+n))) AB z).1 (@hAB z hz).
- split;first by move=>z hz;exact:hz.1.
  split;first by move=>z hz;exact:hz.
  exact:hPoint.
Qed.

(** Source for [current_cartesian_swap_mixed_action]: w#(S times T)
    on every original separated mixed test is (-1)^(kl)
    times the reversed separated action, supporting the
    signed interchange in Federer 4.1.8, p. 361. *)
Theorem current_cartesian_swap_mixed_action i j (S:CA i) (T:CB j) k l
    (e:(k+l)%N=(i+j)%N)
    (alpha:@current_test_space R h2 n B hB k)
    (beta:@current_test_space R h2 m A hA l):
  @current_value R h2 (n+m) BA hBA (i+j)
    (current_cartesian_swap_current (Product i j S T))
    (TrB _ _ e (PureB k l alpha beta))=
    (-1:R)^+(k * l)*@current_value R h2 (m+n) AB hAB (i+j) (Product i j S T)
      (TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)).
Proof.
have hPull:=@current_cartesian_swap_pure_pullback R h2 m n A B hA hB (i+j) k l e alpha beta.
have hPoint z (hz:AB z):
    @current_test_value R h2 (m+n) AB hAB (i+j)
      ((-1:R)^+(k * l)*:TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)) z=
    va (i+j) (pull (i+j) (IB (i+j) (TrB _ _ e (PureB k l alpha beta)))) z.
  exact:(esym (congr1 (fun f:EA (i+j)=>va (i+j) f z) hPull)).
have hAction:=@current_cartesian_swap_action (i+j) (Product i j S T)
  (TrB _ _ e (PureB k l alpha beta))
  ((-1:R)^+(k * l)*:TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)) hPoint.
exact:(eq_trans hAction (linZ (hom_linear (@current_value R h2 (m+n) AB hAB (i+j)
  (Product i j S T))) ((-1:R)^+(k * l))
  (TrA _ _ (eq_trans (addnC l k) e) (PureA l k beta alpha)))).
Qed.
End CurrentCartesianSwapPushforward.
