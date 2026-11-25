(** Federer (1969), 4.1.9, p. 363: evaluate the current
    homotopy identities on original smooth forms for compact
    point-supported currents. The unique smooth-dual extension
    respects equality and the original linear operations.
    All conclusions use its existing public restriction law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCompactExtensionUP
  CurrentCompactExtensionSealed CurrentCompactSmoothValue CurrentSupportGeometry
  CurrentSupportLinearUnion SmoothCompactSet ContinuousRealDual SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCompactSmoothAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU j).
Local Notation ED := (@current_smooth_dual_space R h2 n U hU j).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation support := (@current_support R h2 n U hU j).
Local Notation compact_support T := (@compact (real_norm_metric_space hNX) (support T)).
Local Notation Extension := (@CompactCurrentExtension.value R h2 n j U hU).
Local Notation rho := (@current_smooth_dual_restriction R h2 n U hU j).

(** Source for [current_compact_smooth_congruence]: equal
    compact currents have the same original smooth extension,
    regardless of the compactness proof, supporting the form
    deduction in Federer 4.1.9, p. 363. *)
Theorem current_compact_smooth_congruence (T S:C) (hT:compact_support T) (hS:compact_support S):
  T=S->@current_compact_smooth_value R h2 n j U hU T hT=
    @current_compact_smooth_value R h2 n j U hU S hS.
Proof.
move=>hEqual;subst S.
exact:(@current_compact_smooth_value_independent R h2 n j U hU T hT hS).
Qed.

(** Source for [current_compact_linear_support]: the original
    compactly supported currents form a vector space, supporting
    the current-to-form homotopy passage in Federer 4.1.9,
    p. 363, by 4.1.7, p. 355. *)
Theorem current_compact_linear_support c (T S:C):
  compact_support T->compact_support S->compact_support (c*:T+S:C).
Proof.
move=>hT hS.
pose KT:=@Build_smooth_compact_set R X NX hNX U (support T) (fun x hx=>hx.1) hT.
pose KS:=@Build_smooth_compact_set R X NX hNX U (support S) (fun x hx=>hx.1) hS.
exact:(@current_support_compact_bound R h2 n j U hU
  (smooth_compact_union KT KS) (c*:T+S)
  (@current_support_linear_union R h2 n j U hU c T S)).
Qed.

(** Source for [current_compact_smooth_linear]: the unique
    smooth extension preserves every original linear combination,
    supporting Federer 4.1.9, p. 363. All compactness
    proofs are permitted; no representation hypothesis is added. *)
Theorem current_compact_smooth_linear c (T S:C)
    (hT:compact_support T) (hS:compact_support S)
    (hCombination:compact_support (c*:T+S:C)) (phi:E):
  @current_compact_smooth_value R h2 n j U hU (c*:T+S:C) hCombination phi=
    c*:@current_compact_smooth_value R h2 n j U hU T hT phi+
      @current_compact_smooth_value R h2 n j U hU S hS phi.
Proof.
pose LT:ED:=@CompactCurrentExtension.value R h2 n j U hU T hT.
pose LS:ED:=@CompactCurrentExtension.value R h2 n j U hU S hS.
have hTRestriction:rho LT=T:=@CompactCurrentExtension.laws R h2 n j U hU T hT.
have hSRestriction:rho LS=S:=@CompactCurrentExtension.laws R h2 n j U hU S hS.
have hEqual:(@CompactCurrentExtension.value R h2 n j U hU (c*:T+S:C) hCombination)=
    (c*:LT+LS:ED).
  apply:(@current_compact_extension_unique R h2 n j U hU (c*:T+S:C)).
  - exact:(@CompactCurrentExtension.laws R h2 n j U hU (c*:T+S:C) hCombination).
  - change (rho (c*:LT+LS)=c*:T+S).
    have hLinear:rho (c*:LT+LS)=c*:rho LT+rho LS:=linearP rho c LT LS.
    by rewrite hTRestriction hSRestriction in hLinear.
rewrite /current_compact_smooth_value hEqual.
by rewrite linearP hom_addE hom_scaleE.
Qed.
End CurrentCompactSmoothAlgebra.
