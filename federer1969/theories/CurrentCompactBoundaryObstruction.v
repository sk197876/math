(** Federer (1969), 4.1.7, p. 359:
    no compactly supported current can have
    a single unit point mass as boundary.
    This proves the support obstruction in the
    original half-line example from the earlier
    compact cutoff and actual support laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentCoefficientNorms
  CurrentSpaces CurrentBoundary CurrentSupportGeometry CurrentSupportAgreement CurrentScalarCutoffs
  CurrentTestExteriorDerivative CurrentTestExteriorPlateau CurrentDirac
  SmoothCompactSet SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation SmoothLocalAgreementSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactBoundaryObstruction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation hE1 := (@current_smooth_space_laws R h2 n U hU 1%N).
Local Notation support := (@current_support R h2 n U hU 1%N).

(** Source for [current_compact_boundary_not_dirac]:
    boundary S cannot be delta_c if S
    has compact support in U and c is
    in U, supporting Federer's original
    properness obstruction, 4.1.7, p. 359.
    No finite-mass premise is needed. *)
Theorem current_compact_boundary_not_dirac (S:C 1%N) c:
  U c->compact [set x:real_norm_metric_space hNX|support S x]->
  @current_boundary R h2 n 0%N U hU S<>@dirac_current R h2 n U hU c.
Proof.
move=>hc hCompact hBoundary.
have hIn:(support S `|` [set c]) `<=` U.
  move=>x [hx|->];first exact:hx.1.
  exact:hc.
pose K:=@Build_smooth_compact_set R X NX hNX U
  (support S `|` [set c]) hIn
  (compactU hCompact (@compact_set1 (real_norm_metric_space hNX) c)).
have [gamma [W [hW [hKW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU K.
pose dGamma:=@current_test_exterior_derivative R h2 n 0%N U hU gamma.
have hDZero:forall x,W x->@current_test_value R h2 n U hU 1%N dGamma x=0.
  exact:(@current_test_exterior_plateau_zero R h2 n U hU gamma W (@zero_form R X R^o 1)
    hW hWU hOne).
have hDisjoint:forall x,support S x->~@current_test_support R h2 n 1%N U hU dGamma x.
  move=>x hx.
  exact:(@smooth_support_avoids_open_zero_set R X (A_m X R^o 1) NX hNX
    U (@current_test_space R h2 n U hU 1%N) (@current_test_value R h2 n U hU 1%N)
    dGamma W hW hDZero x (hKW x (or_introl hx))).
have hZero:=@current_test_disjoint_support_zero R h2 n 1%N U hU S dGamma hDisjoint.
have hOneValue:@current_value R h2 n U hU 0%N (@dirac_current R h2 n U hU c) gamma = 1.
  rewrite dirac_current_evaluation (hOne c (hKW c (or_intror (erefl c))));exact:zero_formK.
rewrite -hBoundary current_boundary_evaluation hZero in hOneValue.
by have:=@oner_neq0 R;rewrite -hOneValue eqxx.
Qed.
End CurrentCompactBoundaryObstruction.
