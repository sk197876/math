(** Federer (1969), 4.1.12, p. 367: the
    original dual flat seminorm on actual currents.
    Restrict the already sealed algebraic-functional
    supremum through the actual current evaluation map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet
  CurrentFlatDualSeminormSealed CurrentFlatDualFiniteArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentFlatNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_flat_norm]: F_K on D_m(U)
    is the original sealed dual supremum applied to
    its actual test evaluations, Federer 4.1.12,
    p. 367. It may be infinite. *)
Definition current_flat_norm (T:C): \bar R:=
  @CurrentFlatDualSeminorm.value R h2 n m U hU K (action T).

(** Source for [current_flat_norm_zero]: the zero
    current has original flat seminorm zero,
    supporting Federer 4.1.12, p. 367. *)
Lemma current_flat_norm_zero:current_flat_norm (0:C)=0.
Proof. by rewrite /current_flat_norm linear0 current_flat_dual_zero. Qed.

(** Source for [current_flat_finite_linear_combination]:
    actual currents with finite F_K form the original
    vector subspace, supporting the completeness
    observation in Federer 4.1.12, p. 367. *)
Theorem current_flat_finite_linear_combination c (S T:C):
  (current_flat_norm S < +oo)%E->(current_flat_norm T < +oo)%E->
    (current_flat_norm ((c*:S+T)%R) < +oo)%E.
Proof.
move=>hS hT.
have hValue:action (c*:S+T)=c*:action S+action T:=linearP action c S T.
rewrite /current_flat_norm hValue.
exact:(@current_flat_dual_finite_linear_combination R h2 n m U hU K c (action S) (action T) hS hT).
Qed.
End CurrentFlatNorm.
