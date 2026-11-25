(** Federer (1969), 4.1.24, p. 380: the
    original fixed-K rectifiable currents form an additive
    subgroup of the original flat currents. Approximate
    both summands by the genuine polyhedral source images
    already combined in one source. No arbitrary real
    scalar closure is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed CurrentFiniteMassLinearBound
  RectifiableCurrentApproximationUP RectifiableCurrentWitnesses
  RectifiableCurrentNegate RectifiableImageAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RectifiableCurrentAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).

(** Source for [rectifiable_current_add]: the original subgroup
    is closed under addition, Federer 4.1.24, p. 380.
    Both arbitrarily small mass errors retain the exact
    target K and their original integer source witnesses. *)
Theorem rectifiable_current_add (T S:C):Rect T->Rect S->Rect (T+S).
Proof.
move=>hT hS epsilon hEpsilon.
pose delta:=epsilon/3.
have hDelta:0<delta by rewrite /delta divr_gt0 //;lra.
have[P [hP hTP]]:=hT delta hDelta.
have[Q [hQ hSQ]]:=hS delta hDelta.
exists (P+Q);split;first exact:rectifiable_image_approximant_add hP hQ.
have hBound:=@current_finite_mass_linear_bound R h2 n m U hU 1
  (T-P) (S-Q) delta delta (ltW hTP) (ltW hSQ).
rewrite scale1r normr1 mul1r in hBound.
have hDifference:(T+S)-(P+Q)=(T-P)+(S-Q) by rewrite opprD addrACA.
rewrite hDifference;apply:(le_lt_trans hBound);rewrite lte_fin /delta;lra.
Qed.

(** Source for [rectifiable_current_subgroup]: the full original
    fixed-K additive subgroup assertion in 4.1.24,
    p. 380, from its independently defined approximation
    property and the proved zero, addition and inversion. *)
Theorem rectifiable_current_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 Rect.
Proof.
constructor.
- exact:rectifiable_current_zero.
- exact:rectifiable_current_add.
- exact:rectifiable_current_negate.
Qed.
End RectifiableCurrentAlgebra.
