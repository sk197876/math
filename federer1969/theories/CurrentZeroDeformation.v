(** Federer (1969), 4.1.10, p. 364: the deformation-chain
    contribution of a zero boundary vanishes. Reuse the actual original
    product action and proper pushforward; no support or representation
    assumption is added beyond the homotopy's original properness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianProductAction CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentHomotopyCylinder CurrentHomotopyProductSupport
  CurrentDeformationChainSealed CurrentDeformationChainPushforward CurrentZeroPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentZeroDeformation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu j : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Variable A : set R.
Variables (U : set X) (V : set Y).
Variables (f g : X -> Y) (h : R_n R (1+n)%N -> Y).
Hypothesis hH : @is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h hH.1).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Variable T : @current_space R h2 n U hU j.
Hypothesis hProper : @is_current_homotopy_proper R h2 n nu j A U V f g h hH.1 T.

(** Source for [current_deformation_chain_of_zero]: h#([0,1]
    times T)=0 when T=0, supporting the closed-current cone formula
    in Federer 4.1.10, p. 364. Properness is only on the original
    closed support cylinder and may be proved in any way. *)
Theorem current_deformation_chain_of_zero : T=0 ->
  @CurrentDeformationChain.value R h2 n nu j A U V f g h hH T hProper=0.
Proof.
move=> hZero.
rewrite (@current_deformation_chain_pushforward R h2 n nu j A U V f g h hH T hProper).
apply: current_pushforward_of_zero.
apply: current_values_extensional => psi.
rewrite current_cartesian_product_action hZero.
by rewrite (linear0 (@current_value R h2 n U hU j)) hom_zeroE
  (linear0 (@current_value R h2 (1+n)%N
    (@current_homotopy_product_domain R n A U)
    (@current_cartesian_domain_open R 1%N n AT U hAT hU) (1+j)%N)) hom_zeroE.
Qed.
End CurrentZeroDeformation.
