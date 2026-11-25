(** Federer (1969), 4.1.24, p. 381: inversion
    preserves the original integral and integral-flat classes
    with the same K. These are the inversion parts
    of the printed additive-group assertions; addition and
    the full group carriers remain separate obligations. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary
  RectifiableCurrentApproximationUP RectifiableCurrentNegate IntegralCurrentClassesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section IntegralCurrentNegate.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(fun m=>@current_space R h2 n U hU m).
Local Notation Integral:=(fun m=>@is_integral_current_supported_in R h2 n U hU m K).
Local Notation IntegralFlat:=(fun m=>@is_integral_flat_current_supported_in R h2 n U hU m K).

(** Source for [integral_current_negate_supported]: original
    integral inversion, with the separate zero-degree clause
    and linearity of the positive boundary, 4.1.24, p. 381. *)
Theorem integral_current_negate_supported m (T:C m):Integral m T->Integral m (-T).
Proof.
case:m T=>[|j] T hT;first exact:rectifiable_current_negate hT.
split;first exact:rectifiable_current_negate hT.1.
rewrite -[-T]sub0r (linB (hom_linear (@current_boundary R h2 n j U hU)))
  (lin0 (hom_linear (@current_boundary R h2 n j U hU))) sub0r.
exact:rectifiable_current_negate hT.2.
Qed.

(** Source for [integral_flat_current_negate_supported]: negate
    both original rectifiable terms in R+boundary S,
    retaining exactly K, Federer 4.1.24, p. 381. *)
Theorem integral_flat_current_negate_supported m (T:C m):
  IntegralFlat m T->IntegralFlat m (-T).
Proof.
move=>[A [S [hA [hS hEqual]]]].
exists (-A),(-S);split;first exact:rectifiable_current_negate hA.
split;first exact:rectifiable_current_negate hS.
by rewrite -[-S]sub0r (linB (hom_linear (@current_boundary R h2 n m U hU)))
  (lin0 (hom_linear (@current_boundary R h2 n m U hU))) sub0r -opprD -hEqual.
Qed.
End IntegralCurrentNegate.
