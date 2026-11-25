(** Federer (1969), 4.1.9, p. 363: the degree-zero
    current homotopy identity on original smooth forms for
    compactly supported currents. This is the smooth-dual
    adapter used for the original point-current deduction;
    the earlier test-current identity remains unrestricted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentBoundary
  SmoothCurrentExteriorDerivative SmoothFormPullbackSealed CurrentPushforwardSealed CurrentPushforwardNormality
  CurrentCompactSmoothValue CurrentCompactSmoothAlgebra CurrentCompactBoundarySmooth CurrentCompactPushforwardSmooth
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopySliceClass CurrentHomotopyEndpointProper CurrentHomotopyZeroFormula
  CurrentDeformationChainSealed CurrentDeformationChainCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyZeroSmoothFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h geometry).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu 0%N A U V f g h geometry T.
Hypothesis hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n U hU 0%N T).
Local Notation hpF := (@current_homotopy_start_proper R h2 n nu 0%N A U V f g h geometry T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n nu 0%N A U V f g h geometry T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV T g endpoints.2 classes.2 hpG).
Local Notation hF := (@current_pushforward_compact_support R h2 n nu U V hU hV f endpoints.1 classes.1 0%N T hpF hCompact).
Local Notation hG := (@current_pushforward_compact_support R h2 n nu U V hU hV g endpoints.2 classes.2 0%N T hpG hCompact).
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu 0%N A U V f g h hHomotopy T hProper).
Local Notation hChain := (@current_deformation_chain_compact R h2 n nu 0%N A U V f g h hHomotopy T hCompact hProper).
Local Notation boundary := (@current_boundary R h2 nu 0%N V hV chain).
Local Notation hBoundary := (@current_compact_boundary_compact R h2 nu 0%N V hV chain hChain).
Local Notation E := (@current_smooth_space R h2 nu V hV 0%N).
Local Notation d := (@smooth_current_exterior_derivative R h2 nu 0%N V hV).
Local Notation PullF := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV f endpoints.1 classes.1).
Local Notation PullG := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV g endpoints.2 classes.2).
Local Notation valueT := (@current_compact_smooth_value R h2 n 0%N U hU T hCompact).

(** Source for [current_homotopy_zero_smooth_formula]: the
    compact-current degree-zero homotopy identity extends to
    every original smooth target zero-form, supporting the
    point-current proof in Federer 4.1.9, p. 363.
    The negative-degree boundary term is absent. *)
Theorem current_homotopy_zero_smooth_formula (psi:E):
  valueT (PullG psi)-valueT (PullF psi)=
    @current_compact_smooth_value R h2 nu 1%N V hV chain hChain (d psi).
Proof.
pose hCombination:=@current_compact_linear_support R h2 nu 0%N V hV (-1:R) F G hF hG.
have hEquation:((-1:R)*:F+G:@current_space R h2 nu V hV 0%N)=boundary.
  rewrite scaleN1r addrC.
  exact:(@current_homotopy_zero_formula R h2 n nu A U V f g h hHomotopy T hProper).
have hExtension:=@current_compact_smooth_congruence R h2 nu 0%N V hV
  ((-1:R)*:F+G) boundary hCombination hBoundary hEquation.
have hValue:=congr1 (fun L:Hom E R^o=>L psi) hExtension.
rewrite (@current_compact_smooth_linear R h2 nu 0%N V hV (-1:R) F G hF hG hCombination psi) in hValue.
rewrite (@current_compact_pushforward_smooth_value R h2 n nu 0%N U V hU hV f endpoints.1 classes.1 T hpF hCompact psi)
  (@current_compact_pushforward_smooth_value R h2 n nu 0%N U V hU hV g endpoints.2 classes.2 T hpG hCompact psi)
  (@current_compact_boundary_smooth_value R h2 nu 0%N V hV chain hChain psi) in hValue.
by move:hValue;rewrite scaleN1r addrC.
Qed.
End CurrentHomotopyZeroSmoothFormula.
