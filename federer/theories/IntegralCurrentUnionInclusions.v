(** Federer (1969), 4.1.24, p. 381: every
    arrow in the original inclusion diagram on the
    literal compact unions. Retain the distinction between
    integral polyhedral chains and the real polyhedral
    span. The finite mass of the rectifiable and
    normal terms is a conclusion, not an extra
    premise. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed NormalCurrentsUP FlatCurrentsUP
  PolyhedralCurrentAlgebra PolyhedralCurrentUnion PolyhedralNormal
  RectifiableCurrentApproximationUP RectifiableCurrentBasic IntegralCurrentClassesUP
  IntegralCurrentInclusions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section IntegralCurrentUnionInclusions.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Rect:=(@is_rectifiable_current R h2 n U hU m).
Local Notation Int:=(@is_integral_current R h2 n U hU m).
Local Notation IF:=(@is_integral_flat_current R h2 n U hU m).
Local Notation PolyInt:=(@is_integral_polyhedral_current R h2 n m U hU).
Local Notation PolyReal:=(@is_polyhedral_current R h2 n m U hU).
Local Notation Normal:=(@is_normal_current R h2 n U hU m).
Local Notation Flat:=(@is_flat_current R h2 n m U hU).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).

(** Source for [integral_polyhedral_current_is_integral]: the
    first original top-row arrow on compact unions,
    4.1.24, p. 381. *)
Theorem integral_polyhedral_current_is_integral (T:C):PolyInt T->Int T.
Proof.
move=>[K hT];exists K;exact:integral_polyhedral_current_integral_supported hT.
Qed.

(** Source for [integral_current_is_rectifiable]: the original
    integral-to-rectifiable union inclusion, 4.1.24, p. 381. *)
Theorem integral_current_is_rectifiable (T:C):Int T->Rect T.
Proof.
move=>[K hT];exists K;exact:integral_current_is_rectifiable_supported hT.
Qed.

(** Source for [rectifiable_current_is_integral_flat]: the
    last original top-row arrow, 4.1.24, p. 381. *)
Theorem rectifiable_current_is_integral_flat (T:C):Rect T->IF T.
Proof.
move=>[K hT];exists K;exact:rectifiable_current_is_integral_flat_supported hT.
Qed.

(** Source for [integral_polyhedral_current_is_real_polyhedral]: the
    first original vertical arrow is into the real
    algebraic span, 4.1.24, p. 381. *)
Theorem integral_polyhedral_current_is_real_polyhedral (T:C):PolyInt T->PolyReal T.
Proof. exact:integral_polyhedral_union_is_polyhedral. Qed.

(** Source for [real_polyhedral_current_is_normal]: the first
    original bottom-row arrow on compact unions,
    4.1.24, p. 381. *)
Theorem real_polyhedral_current_is_normal (T:C):PolyReal T->Normal T.
Proof.
move=>[K hT];exact:(@real_polyhedral_current_normal_support R h2 n m U hU K T hT).1.
Qed.

(** Source for [integral_current_is_normal]: the second
    original vertical arrow, 4.1.24, p. 381,
    derives both representations and compactness. *)
Theorem integral_current_is_normal (T:C):Int T->Normal T.
Proof.
move=>[K hT];exact:(@integral_current_normal_supported R h2 n U hU K m T hT).1.
Qed.

(** Source for [rectifiable_current_is_flat_finite_mass]: the
    third original vertical arrow retains actual finite
    mass, 4.1.24, p. 381. *)
Theorem rectifiable_current_is_flat_finite_mass (T:C):Rect T->Flat T /\(M T< +oo)%E.
Proof.
move=>[K hT];split.
- exists K;exact:rectifiable_current_flat_supported hT.
- exact:rectifiable_current_finite_mass hT.
Qed.

(** Source for [integral_flat_current_is_flat]: the last
    original vertical arrow, 4.1.24, p. 381,
    with no finite mass assertion about its input. *)
Theorem integral_flat_current_is_flat (T:C):IF T->Flat T.
Proof.
move=>[K hT];exists K;exact:integral_flat_current_is_flat_supported hT.
Qed.

(** Source for [normal_current_is_flat_finite_mass]: the middle
    original bottom-row arrow, 4.1.24, p. 381.
    The final bottom-row inclusion simply discards the
    proved finite-mass conjunct. *)
Theorem normal_current_is_flat_finite_mass (T:C):Normal T->Flat T /\(M T< +oo)%E.
Proof. exact:normal_current_flat_finite_mass. Qed.
End IntegralCurrentUnionInclusions.
