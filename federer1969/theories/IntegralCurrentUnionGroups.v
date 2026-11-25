(** Federer (1969), 4.1.24, pp. 380–381:
    each original compact union is an additive group.
    The compact union of two witness indices carries
    both summands by the already proved monotonicity
    laws. No chosen exhaustion or common support-only
    definition replaces the original unions. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces RectifiableCurrentApproximationUP
  RectifiableCurrentWitnesses RectifiableCurrentNegate RectifiableCurrentAlgebra
  IntegralCurrentClassesUP IntegralCurrentNegate IntegralCurrentAlgebra IntegralCurrentMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section IntegralCurrentUnionGroups.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Rect:=(@is_rectifiable_current R h2 n U hU m).
Local Notation Integral:=(@is_integral_current R h2 n U hU m).
Local Notation IntegralFlat:=(@is_integral_flat_current R h2 n U hU m).
Local Notation Empty:=(@smooth_compact_empty R X
  (inner_norm (@euclidean_inner_productP R n)) hNX U).

(** Source for [rectifiable_current_union_subgroup]: the original
    rectifiable compact union is an additive group,
    4.1.24, pp. 380–381, including empty U. *)
Theorem rectifiable_current_union_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 Rect.
Proof.
constructor.
- exists Empty;exact:rectifiable_current_zero.
- move=>T S [K hT] [L hS];exists (smooth_compact_union K L).
  apply:rectifiable_current_add.
  + apply:(@rectifiable_current_compact_monotone R h2 n U hU K
      (smooth_compact_union K L) (fun x hx=>or_introl hx) m T hT).
  + apply:(@rectifiable_current_compact_monotone R h2 n U hU L
      (smooth_compact_union K L) (fun x hx=>or_intror hx) m S hS).
- move=>T [K hT];exists K;exact:rectifiable_current_negate hT.
Qed.

(** Source for [integral_current_union_subgroup]: the original
    union of all compact integral groups is an
    additive group, Federer 4.1.24, p. 381. *)
Theorem integral_current_union_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 Integral.
Proof.
constructor.
- exists Empty;exact:integral_current_zero_supported.
- move=>T S [K hT] [L hS];exists (smooth_compact_union K L).
  apply:integral_current_add_supported.
  + exact:(@integral_current_compact_monotone R h2 n U hU K
      (smooth_compact_union K L) (fun x hx=>or_introl hx) m T hT).
  + exact:(@integral_current_compact_monotone R h2 n U hU L
      (smooth_compact_union K L) (fun x hx=>or_intror hx) m S hS).
- move=>T [K hT];exists K;exact:integral_current_negate_supported hT.
Qed.

(** Source for [integral_flat_current_union_subgroup]: the original
    integral-flat compact union is an additive group,
    Federer 4.1.24, p. 381. Every decomposition
    retains one common compact after taking the union. *)
Theorem integral_flat_current_union_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 IntegralFlat.
Proof.
constructor.
- exists Empty;exact:integral_flat_current_zero_supported.
- move=>T S [K hT] [L hS];exists (smooth_compact_union K L).
  apply:integral_flat_current_add_supported.
  + exact:(@integral_flat_current_compact_monotone R h2 n U hU K
      (smooth_compact_union K L) (fun x hx=>or_introl hx) m T hT).
  + exact:(@integral_flat_current_compact_monotone R h2 n U hU L
      (smooth_compact_union K L) (fun x hx=>or_intror hx) m S hS).
- move=>T [K hT];exists K;exact:integral_flat_current_negate_supported hT.
Qed.
End IntegralCurrentUnionGroups.
