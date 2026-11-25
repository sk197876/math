(** Federer (1969), 4.1.14, p. 371: the local
    cutoff definition agrees with the previously defined
    image of every compact flat current. A single scalar
    cutoff equals one near the entire support. The
    original plateau law supplies the identity internally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP SmoothCompactSet
  CurrentSpaces CurrentContraction CurrentEvaluation CurrentScalarCutoffs
  CurrentScalarSupportPlateau CurrentSupportGeometry FlatCurrentsUP
  FlatCurrentFinite SmoothTestSpaces SmoothTestEvaluation
  CurrentLipschitzPushforwardUP CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImageCompactAgreement.
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
Local Notation inc := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N)).
Local Notation Global := (@CurrentFlatLipschitzPushforward.value R h2 n nu m
  U V hU hV f hImage hLocal).

(** Source for [current_lipschitz_image_compact_agreement]: the
    original local image agrees with the compact flat image,
    Federer 4.1.14, p. 371. No additional properness,
    normality, finite-mass or representation premise is required
    for this consequence of the independent action law. *)
Theorem current_lipschitz_image_compact_agreement
    (T : CU) (hFlat : @is_flat_current R h2 n m U hU T) (Q : CV) :
  @is_current_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal T Q -> Q=Global T hFlat.
Proof.
move=> hQ.
have [K hK] := hFlat.
have hSupport := @flat_current_supported_support R h2 n m U hU K T hK.
have [gamma [W [hW [hKW [hWU hOne]]]]] :=
  @current_compact_scalar_cutoff R h2 n U hU K.
have hTW : @current_support R h2 n U hU m T `<=` W.
  move=> x hx; exact: hKW x (hSupport x hx).
have hOneSmooth : forall x, W x ->
    @current_smooth_value R h2 n U hU 0%N (inc gamma) x=@zero_form R X R^o 1.
  move=> x hx; exact: hOne x hx.
have hPlateau := @current_scalar_support_plateau R h2 n m U hU
  T (inc gamma) W hW hTW hWU hOneSmooth.
pose S := @current_contraction R h2 n 0%N m U hU (inc gamma) T.
have hS : @is_flat_current R h2 n m U hU S.
  rewrite /S -hPlateau; exact: hFlat.
have hEquality : Global S hS=Global T hFlat.
  exact: (@current_flat_lipschitz_pushforward_congruence R h2 n nu m
    U V hU hV f hImage hLocal S T hS hFlat (esym hPlateau)).
apply: (@current_values_extensional R h2 nu m V hV)=> phi.
have hCutoff : @is_current_lipschitz_pushforward_cutoff R h2 n nu m
    U V hU hV T f phi gamma.
  move=> x hx _.
  have hNear := open_nbhs_nbhs (conj hW (hTW x hx)).
  apply: (filterS _ hNear)=> z hz; exact: hOne z hz.
have hAction := (proj2 hQ) phi gamma hS hCutoff.
by rewrite hEquality in hAction.
Qed.
End CurrentLipschitzImageCompactAgreement.
