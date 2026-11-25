(** Federer (1969), 4.1.14, p. 371: the
    original locally flat Lipschitz image commutes
    with positive-degree boundary. Choose one compact
    scalar cutoff over the target test support.
    Its derivative contributes nothing there because
    the cutoff is one on an open neighbourhood
    of the relevant original source support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingZero LipschitzUP SmoothCompactSet
  CurrentSpaces CurrentSupportGeometry CurrentSupportAgreement CurrentSupportLinearUnion
  CurrentBoundary CurrentBoundarySupport CurrentTestExteriorDerivative
  CurrentContraction CurrentContractionSupport CurrentEvaluation CurrentPointEvaluation
  CurrentScalarCutoffs CurrentScalarPlateau CurrentProperSupport
  SmoothTestSpaces SmoothTestEvaluation FlatCurrentsUP FlatCurrentUnion
  CurrentLocallyFlatBoundary CurrentFlatLipschitzPushforwardSealed
  CurrentFlatLipschitzPushforwardBasic CurrentFlatLipschitzPushforwardBoundary
  CurrentLipschitzPushforwardUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLipschitzImageBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Local Notation C d:=(@current_space R h2 n U hU d).
Local Notation D d:=(@current_space R h2 nu V hV d).
Local Notation bd:=(@current_boundary R h2 n m U hU).
Local Notation targetBd:=(@current_boundary R h2 nu m V hV).
Local Notation inc:=(smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N)).
Local Notation scalar:=(@current_smooth_value R h2 n U hU 0%N).
Local Notation contract d gamma:=(@current_contraction R h2 n 0%N d U hU (inc gamma)).
Local Notation Global d:=(@CurrentFlatLipschitzPushforward.value R h2 n nu d
  U V hU hV f hImage hLocal).

(** Source for [current_lipschitz_image_boundary]:
    boundary(f#T)=f#(boundary T) on original
    locally flat currents, Federer 4.1.14, p. 371.
    Properness is required only on spt T.
    Normality and finite mass are not assumed. *)
Theorem current_lipschitz_image_boundary (T:C m.+1) (Q:D m.+1) (P:D m):
  @is_locally_flat_current R h2 n m.+1 U hU T ->
  @is_current_proper_on_support R h2 n nu m.+1 U hU V T f hImage ->
  @is_current_lipschitz_image R h2 n nu m.+1 U V hU hV f hImage hLocal T Q ->
  @is_current_lipschitz_image R h2 n nu m U V hU hV f hImage hLocal (bd T) P ->
  targetBd Q = P.
Proof.
move=>hT hProper hQ hP.
pose hBoundaryLocal:=@locally_flat_current_boundary R h2 n m U hU T hT.
apply:(@current_values_extensional R h2 nu m V hV)=>phi.
have[K hPhi]:=smooth_test_support_bound (@current_smooth_space_laws R h2 nu V hV m) phi.
pose L:=@current_proper_support_compact_locus R h2 n nu m.+1 U hU V
  T f hImage hProper K.
have[gamma [W [hW [hLW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU L.
pose RT:=contract m.+1 gamma T.
pose RB:=contract m gamma (bd T).
pose BRT:=bd RT.
pose hRT:=hT gamma.
pose hRB:=hBoundaryLocal gamma.
pose hBRT:=@flat_current_boundary R h2 n m U hU RT hRT.
have hPlateau x (hx:@current_support R h2 n U hU m.+1 T x)
    (hTarget:@current_test_support R h2 nu m V hV phi (f x)):
    @interior (real_norm_metric_space hNX)
      [set z|@current_test_value R h2 n U hU 0%N gamma z=@zero_form R X R^o 1] x.
  have hL:smooth_compact_carrier L x:=conj hx (hPhi (f x) hTarget).
  have hNear:=open_nbhs_nbhs (conj hW (hLW x hL)).
  apply:(filterS _ hNear)=>z hz;exact:hOne z hz.
pose dPhi:=@current_test_exterior_derivative R h2 nu m V hV phi.
have hCutT:@is_current_lipschitz_pushforward_cutoff R h2 n nu m.+1
    U V hU hV T f dPhi gamma.
  move=>x hx hTarget.
  exact:(@hPlateau x hx
    (@current_test_exterior_support_subset R h2 nu m V hV phi (f x) hTarget)).
have hCutB:@is_current_lipschitz_pushforward_cutoff R h2 n nu m
    U V hU hV (bd T) f phi gamma.
  move=>x hx hTarget.
  exact:(@hPlateau x
    (@current_boundary_support_subset R h2 n m U hU T x hx) hTarget).
pose Difference:=BRT-RB.
have hDifference:@is_flat_current R h2 n m U hU Difference.
  have h:=@flat_current_linear_combination R h2 n m U hU (-1) RB BRT hRB hBRT.
  by rewrite scaleN1r addrC in h.
have hDifferenceSupport:@current_support R h2 n U hU m Difference `<=`
    @current_support R h2 n U hU m.+1 T.
  move=>x hx.
  have hUnion:=@current_support_linear_union R h2 n m U hU (-1) RB BRT.
  have hSupport:@current_support R h2 n U hU m ((-1:R)*:RB+BRT) x.
    by rewrite scaleN1r addrC.
  case:(hUnion x hSupport)=>[hRBx|hBRTx].
  - apply:(@current_boundary_support_subset R h2 n m U hU T x).
    exact:(@current_contraction_support_subset R h2 n 0%N m U hU (inc gamma) (bd T) x hRBx).
  - apply:(@current_contraction_support_subset R h2 n 0%N m.+1 U hU (inc gamma) T x).
    exact:(@current_boundary_support_subset R h2 n m U hU RT x hBRTx).
have hAway:forall x,@current_support R h2 n U hU m Difference x ->
    ~@current_test_support R h2 nu m V hV phi (f x).
  move=>x hx hTarget.
  pose O:=@interior (real_norm_metric_space hNX)
    [set z|@current_test_value R h2 n U hU 0%N gamma z=@zero_form R X R^o 1].
  have hO:@open (real_norm_metric_space hNX) O:=open_interior _.
  have hOneO:forall y,O y->scalar (inc gamma) y=@zero_form R X R^o 1.
    move=>y hy;exact:interior_subset hy.
  have hAgreement:forall psi:@current_test_space R h2 n U hU m,
      @current_test_support R h2 n m U hU psi `<=` O ->
      @current_value R h2 n U hU m BRT psi=@current_value R h2 n U hU m RB psi.
    move=>psi hPsi.
    rewrite /BRT /RT /RB current_boundary_evaluation !current_contraction_evaluation.
    have hDPsi:@current_test_support R h2 n m.+1 U hU
        (@current_test_exterior_derivative R h2 n m U hU psi) `<=` O.
      move=>z hz;apply:hPsi;exact:(@current_test_exterior_support_subset R h2 n m U hU psi z hz).
    rewrite (@current_scalar_test_local_plateau R h2 n m.+1 U hU O (inc gamma)
      hOneO _ hDPsi).
    rewrite (@current_scalar_test_local_plateau R h2 n m U hU O (inc gamma)
      hOneO psi hPsi).
    exact:(esym (@current_boundary_evaluation R h2 n m U hU T psi)).
  have hOutside:=@current_support_difference_agreement R h2 n m U hU BRT RB O hO hAgreement.
  apply:(hOutside x hx).2.
  exact:(@hPlateau x (hDifferenceSupport x hx) hTarget).
have hTargetAway:forall y,@current_support R h2 nu V hV m (Global m Difference hDifference) y ->
    ~@current_test_support R h2 nu m V hV phi y.
  move=>y hy.
  have[x hx <-]:=@current_flat_lipschitz_pushforward_support R h2 n nu m U V hU hV
    f hImage hLocal Difference hDifference y hy.
  exact:hAway x hx.
have hZero:=@current_test_disjoint_support_zero R h2 nu m V hV
  (Global m Difference hDifference) phi hTargetAway.
have hSubtract:=@current_flat_lipschitz_pushforward_subtract R h2 n nu m U V hU hV
  f hImage hLocal BRT RB hBRT hRB hDifference.
rewrite hSubtract in hZero.
pose Eval:=@current_point_evaluation R h2 nu m V hV phi.
change (Eval (Global m BRT hBRT-Global m RB hRB)=0) in hZero.
rewrite (linB (hom_linear Eval)) in hZero.
have hValues:Eval (Global m BRT hBRT)=Eval (Global m RB hRB).
  apply/eqP;rewrite -subr_eq0;exact/eqP.
change (@current_value R h2 nu V hV m (Global m BRT hBRT) phi=
  @current_value R h2 nu V hV m (Global m RB hRB) phi) in hValues.
rewrite current_boundary_evaluation (hQ.2 dPhi gamma hRT hCutT).
rewrite -current_boundary_evaluation
  (@current_flat_lipschitz_pushforward_boundary R h2 n nu m U V hU hV
    f hImage hLocal RT hRT hBRT).
rewrite hValues.
exact:esym (hP.2 phi gamma hRB hCutB).
Qed.
End CurrentLipschitzImageBoundary.
