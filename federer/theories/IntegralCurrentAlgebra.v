(** Federer (1969), 4.1.24, p. 381: the
    original fixed-K integral and integral-flat classes
    are additive subgroups. Their independent definitions
    use only original rectifiable membership and actual
    boundary, with a separate zero-degree integral clause. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom Bilinear TopologicalGroupUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary RectifiableCurrentApproximationUP
  RectifiableCurrentWitnesses RectifiableCurrentAlgebra IntegralCurrentClassesUP IntegralCurrentNegate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section IntegralCurrentAlgebra.
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

(** Source for [integral_current_zero_supported]: the original
    integral group contains zero in every degree,
    with the same K, 4.1.24, p. 381. *)
Theorem integral_current_zero_supported m:Integral m (0:C m).
Proof.
case:m=>[|j];first exact:rectifiable_current_zero.
split;first exact:rectifiable_current_zero.
rewrite (lin0 (hom_linear (@current_boundary R h2 n j U hU))).
exact:rectifiable_current_zero.
Qed.

(** Source for [integral_current_add_supported]: both original
    rectifiable conditions, or the separate degree-zero one,
    are preserved by addition, 4.1.24, p. 381. *)
Theorem integral_current_add_supported m (T S:C m):
  Integral m T->Integral m S->Integral m (T+S).
Proof.
case:m T S=>[|j] T S hT hS;first exact:rectifiable_current_add hT hS.
split;first exact:rectifiable_current_add hT.1 hS.1.
rewrite (linD (hom_linear (@current_boundary R h2 n j U hU))).
exact:rectifiable_current_add hT.2 hS.2.
Qed.

(** Source for [integral_current_subgroup_supported]: the original
    fixed-K integral class is an additive group,
    Federer 4.1.24, p. 381. No real scaling
    is introduced. *)
Theorem integral_current_subgroup_supported m:
  is_subgroup (fun T S:C m=>T+S) (fun T=>-T) 0 (Integral m).
Proof.
constructor.
- exact:integral_current_zero_supported.
- exact:integral_current_add_supported.
- exact:integral_current_negate_supported.
Qed.

(** Source for [integral_flat_current_zero_supported]: the two
    original zero rectifiable terms witness integral-flat
    zero, Federer 4.1.24, p. 381. *)
Theorem integral_flat_current_zero_supported m:IntegralFlat m (0:C m).
Proof.
exists (0:C m),(0:C m.+1);split;first exact:rectifiable_current_zero.
split;first exact:rectifiable_current_zero.
by rewrite (lin0 (hom_linear (@current_boundary R h2 n m U hU))) addr0.
Qed.

(** Source for [integral_flat_current_add_supported]: add both
    original same-K rectifiable terms, then use actual
    boundary linearity, 4.1.24, p. 381. This
    does not require finite mass of the resulting current. *)
Theorem integral_flat_current_add_supported m (T S:C m):
  IntegralFlat m T->IntegralFlat m S->IntegralFlat m (T+S).
Proof.
move=>[A [B [hA [hB ->]]]] [P [Q [hP [hQ ->]]]].
exists (A+P),(B+Q);split;first exact:rectifiable_current_add hA hP.
split;first exact:rectifiable_current_add hB hQ.
by rewrite (linD (hom_linear (@current_boundary R h2 n m U hU))) addrACA.
Qed.

(** Source for [integral_flat_current_subgroup_supported]: the
    literal original integral-flat decompositions form an
    additive group with exactly K, 4.1.24, p. 381. *)
Theorem integral_flat_current_subgroup_supported m:
  is_subgroup (fun T S:C m=>T+S) (fun T=>-T) 0 (IntegralFlat m).
Proof.
constructor.
- exact:integral_flat_current_zero_supported.
- exact:integral_flat_current_add_supported.
- exact:integral_flat_current_negate_supported.
Qed.
(** Source for [integral_flat_current_subtract_supported]: every
    actual original sequence increment remains in the
    same integral-flat group, 4.1.24, p. 382. *)
Theorem integral_flat_current_subtract_supported m (T S:C m):
  IntegralFlat m T->IntegralFlat m S->IntegralFlat m (T-S).
Proof.
move=>hT hS;apply:integral_flat_current_add_supported hT _.
exact:integral_flat_current_negate_supported hS.
Qed.
End IntegralCurrentAlgebra.
