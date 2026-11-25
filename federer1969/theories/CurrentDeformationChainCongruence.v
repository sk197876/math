(** Federer (1969), 4.1.18, p. 374: equal
    actual current inputs give the same old
    smooth deformation, independently of the original
    support-properness evidence. This is a direct
    public uniqueness consequence.  *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentDeformationChainSealed CurrentDeformationChainExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDeformationChainCongruence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU:=(@current_homotopy_source_open R n nu A U V f g h hH.1).
Variables T S:@current_space R h2 n U hU m.
Hypothesis hT:@is_current_homotopy_proper R h2 n nu m A U V f g h hH.1 T.
Hypothesis hS:@is_current_homotopy_proper R h2 n nu m A U V f g h hH.1 S.

(** Source for [current_deformation_chain_current_congruence]:
    only the original current and map determine
    h#([0,1] times T), by 4.1.9, p. 363,
    as required for 4.1.18, p. 374. *)
Theorem current_deformation_chain_current_congruence:
  T=S ->
  @CurrentDeformationChain.value R h2 n nu m A U V f g h hH T hT=
  @CurrentDeformationChain.value R h2 n nu m A U V f g h hH S hS.
Proof.
move=>hEqual;subst S.
apply:(@current_deformation_chain_unique R h2 n nu m A U V f g h hH T hT).
- exact:(@CurrentDeformationChain.laws R h2 n nu m A U V f g h hH T hT).
- exact:(@CurrentDeformationChain.laws R h2 n nu m A U V f g h hH T hS).
Qed.
End CurrentDeformationChainCongruence.
