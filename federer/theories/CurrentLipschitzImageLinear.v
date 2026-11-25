(** Federer (1969), 4.1.14, p. 371: the local
    Lipschitz pushforward is linear. Choose one compact
    scalar cutoff for the two original support preimage
    loci of the target test, then use actual contraction
    and compact flat-image linearity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP SmoothCompactSet
  CurrentSpaces CurrentContraction CurrentEvaluation CurrentPointEvaluation
  CurrentScalarCutoffs CurrentSupportGeometry CurrentSupportLinearUnion
  CurrentProperSupport CurrentProperSupportLinear FlatCurrentsUP FlatCurrentUnion
  SmoothTestSpaces SmoothTestEvaluation CurrentLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImageLinear.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu m : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U : set X) (V : set Y).
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Hypothesis hV : forall y, V y -> norm_domain_interior NY V y.
Variable f : X -> Y.
Hypothesis hImage : forall x, U x -> V (f x).
Hypothesis hLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Local Notation CU := (@current_space R h2 n U hU m).
Local Notation CV := (@current_space R h2 nu V hV m).
Local Notation LocalFlat := (@is_locally_flat_current R h2 n m U hU).
Local Notation Proper := (fun T:CU =>
  @is_current_proper_on_support R h2 n nu m U hU V T f hImage).
Local Notation Image := (@is_current_lipschitz_image R h2 n nu m
  U V hU hV f hImage hLocal).
Local Notation Global := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal).
Local Notation hScalar := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation inc := (smooth_test_inclusion hScalar).
Local Notation contract gamma :=
  (@current_contraction R h2 n 0%N m U hU (inc gamma)).

(** Source for [current_lipschitz_image_linear]: the original
    local image preserves cT+S, Federer 4.1.14,
    p. 371, with properness only on the two actual
    supports. Local flatness and properness of the combination
    follow from preceding laws; they are not extra premises. *)
Theorem current_lipschitz_image_linear c (T S : CU) (QT QS QC : CV) :
  LocalFlat T -> LocalFlat S -> Proper T -> Proper S ->
  Image T QT -> Image S QS -> Image (c*:T+S) QC ->
  QC=c*:QT+QS.
Proof.
move=> hT hS hProperT hProperS hQT hQS hQC.
have hCombination := @locally_flat_current_linear_combination R h2 n m U hU
  c T S hT hS.
apply: (@current_values_extensional R h2 nu m V hV)=> phi.
have [K hPhi] := smooth_test_support_bound
  (@current_smooth_space_laws R h2 nu V hV m) phi.
pose LT := @current_proper_support_compact_locus R h2 n nu m U hU V
  T f hImage hProperT K.
pose LS := @current_proper_support_compact_locus R h2 n nu m U hU V
  S f hImage hProperS K.
pose L := smooth_compact_union LT LS.
have [gamma [W [hW [hLW [hWU hOne]]]]] :=
  @current_compact_scalar_cutoff R h2 n U hU L.
have hPlateau : forall x,
    (@current_support R h2 n U hU m T x \/
      @current_support R h2 n U hU m S x) ->
    @current_test_support R h2 nu m V hV phi (f x) ->
    @interior (real_norm_metric_space hNX)
      [set z | @current_test_value R h2 n U hU 0%N gamma z=
        @zero_form R X R^o 1] x.
  move=> x hx hTarget.
  have hInL : smooth_compact_carrier L x.
    case: hx=> hx.
    - left; exact: (conj hx (hPhi (f x) hTarget)).
    - right; exact: (conj hx (hPhi (f x) hTarget)).
  have hNear := open_nbhs_nbhs (conj hW (hLW x hInL)).
  apply: (filterS _ hNear)=> z hz; exact: hOne z hz.
have hCutT : @is_current_lipschitz_pushforward_cutoff R h2 n nu m
    U V hU hV T f phi gamma.
  move=> x hx; exact: @hPlateau x (or_introl hx).
have hCutS : @is_current_lipschitz_pushforward_cutoff R h2 n nu m
    U V hU hV S f phi gamma.
  move=> x hx; exact: @hPlateau x (or_intror hx).
have hCutC : @is_current_lipschitz_pushforward_cutoff R h2 n nu m
    U V hU hV (c*:T+S) f phi gamma.
  move=> x hx.
  exact: @hPlateau x (@current_support_linear_union R h2 n m U hU c T S x hx).
pose RT := contract gamma T.
pose RS := contract gamma S.
pose RC := contract gamma (c*:T+S).
pose hRT := hT gamma.
pose hRS := hS gamma.
pose hRC := hCombination gamma.
have hContract : RC=c*:RT+RS.
  exact: (linearP (contract gamma)).
pose hFlatCombination := @flat_current_linear_combination R h2 n m U hU
  c RT RS hRT hRS.
have hGlobal : Global RC hRC=c*:Global RT hRT+Global RS hRS.
  have hEqual := @current_flat_lipschitz_pushforward_congruence R h2 n nu m
    U V hU hV f hImage hLocal RC (c*:RT+RS) hRC hFlatCombination hContract.
  have hLinear := @current_flat_lipschitz_pushforward_linear R h2 n nu m
    U V hU hV f hImage hLocal c RT RS hRT hRS.
  exact: eq_trans hEqual hLinear.
have hValueT := (proj2 hQT) phi gamma hRT hCutT.
have hValueS := (proj2 hQS) phi gamma hRS hCutS.
have hValueC := (proj2 hQC) phi gamma hRC hCutC.
rewrite hGlobal in hValueC.
pose E := @current_point_evaluation R h2 nu m V hV phi.
change (E QC=E (c*:QT+QS)).
change (E QC=E (c*:Global RT hRT+Global RS hRS)) in hValueC.
change (E QT=E (Global RT hRT)) in hValueT.
change (E QS=E (Global RS hRS)) in hValueS.
have hGlobalPoint : E (c*:Global RT hRT+Global RS hRS)=
    c*:E (Global RT hRT)+E (Global RS hRS).
  exact ((hom_linear E) c (Global RT hRT) (Global RS hRS)).
have hTargetPoint : E (c*:QT+QS)=c*:E QT+E QS.
  exact ((hom_linear E) c QT QS).
have hCombined : c*:E QT+E QS=c*:E (Global RT hRT)+E (Global RS hRS).
  exact:(congr2 (fun a b:R^o=>c*:a+b) hValueT hValueS).
exact:eq_trans hValueC (eq_trans hGlobalPoint (esym (eq_trans hTargetPoint hCombined))).
Qed.
End CurrentLipschitzImageLinear.
