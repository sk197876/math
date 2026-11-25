(** Federer (1969), 4.1.12, p. 367: the
    finite dual flat functionals form a vector
    subspace. Reuse the exact original homogeneous
    bound; no topology or support hypothesis is added. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet ExtendedSupremumUP
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed
  SeminormFunctionalUnitBound CurrentFlatDualSeminormBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatDualFiniteArithmetic.
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
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation F := (@current_flat_test_seminorm R h2 n m U hU K).

Local Notation hF := (@current_flat_test_is_seminorm R h2 n m U hU K).
Local Notation Dual := (@CurrentFlatDualSeminorm.value R h2 n m U hU K).
Local Notation hDual := (@CurrentFlatDualSeminorm.laws R h2 n m U hU K).

(** Source for [current_flat_dual_zero]: the original
    flat seminorm of the zero functional is zero,
    supporting Federer 4.1.12, p. 367, including
    empty compact sets and empty open domains. *)
Lemma current_flat_dual_zero:Dual (0:Hom DT R^o)=0.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split.
- apply:(@current_flat_dual_upper_from_bound R h2 n m U hU K (0:Hom DT R^o) (0:R)
    (lexx (0:R)))=>phi.
  by rewrite hom_zeroE normr0 mul0r.
- exact:current_flat_dual_nonnegative.
Qed.

(** Source for [current_flat_dual_finite_from_bound]: a
    finite homogeneous flat bound gives a finite
    original dual value, supporting Federer 4.1.12,
    p. 367. The coefficient may be zero. *)
Lemma current_flat_dual_finite_from_bound (T:Hom DT R^o) c:
  0<=c->(forall phi,`|T phi|<=c * F phi)->(Dual T < +oo)%E.
Proof.
move=>hc hBound.
exact:(le_lt_trans (@current_flat_dual_upper_from_bound R h2 n m U hU K T c hc hBound)
  (ltry c)).
Qed.

(** Source for [current_flat_dual_finite_linear_combination]:
    the algebraic finite-flat functionals form a
    vector subspace, supporting the completeness
    observation in Federer 4.1.12, p. 367. *)
Theorem current_flat_dual_finite_linear_combination c (S T:Hom DT R^o):
  (Dual S < +oo)%E->(Dual T < +oo)%E->(Dual ((c*:S+T)%R) < +oo)%E.
Proof.
move=>hS hT.
have [a [ha hA]]:=@current_flat_dual_finite_value R h2 n m U hU K S hS.
have [b [hb hB]]:=@current_flat_dual_finite_value R h2 n m U hU K T hT.
have hSB:=@current_flat_dual_finite_bound R h2 n m U hU K S a hA.
have hTB:=@current_flat_dual_finite_bound R h2 n m U hU K T b hB.
apply:(@current_flat_dual_finite_from_bound (c*:S+T) (`|c| * a+b)).
- exact:addr_ge0 (mulr_ge0 (normr_ge0 c) ha) hb.
- move=>phi.
  have hValue:(c*:S+T) phi=c * S phi+T phi by rewrite hom_addE hom_scaleE.
  rewrite hValue.
  apply:(le_trans (ler_normD (c * S phi) (T phi))).
  rewrite normrM mulrDl -mulrA.
  exact:(lerD (ler_wpM2l (normr_ge0 c) (hSB phi)) (hTB phi)).
Qed.
End CurrentFlatDualFiniteArithmetic.
