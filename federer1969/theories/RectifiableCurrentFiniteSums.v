(** Federer (1969), 4.1.24, p. 382: every
    original finite prefix of a rectifiable series
    is rectifiable with the same K. Its difference
    terms stay in that group. These algebraic laws
    support both exact cost series in the original
    completeness proof. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces RectifiableCurrentApproximationUP
  RectifiableCurrentWitnesses RectifiableCurrentNegate RectifiableCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section RectifiableCurrentFiniteSums.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Rect:=(@is_rectifiable_current_supported_in R h2 n m U hU K).

(** Source for [rectifiable_current_subtract]: original fixed-K
    differences remain rectifiable in the series argument,
    4.1.24, p. 382. *)
Theorem rectifiable_current_subtract (T S:C):Rect T->Rect S->Rect (T-S).
Proof.
move=>hT hS;apply:rectifiable_current_add hT _.
exact:rectifiable_current_negate hS.
Qed.

(** Source for [rectifiable_current_prefix]: every finite
    original series prefix lies in exactly R_(m,K),
    including the zero prefix, 4.1.24, p. 382. *)
Theorem rectifiable_current_prefix (v:nat->C):
  (forall i,Rect (v i))->forall k,Rect (\sum_(i<k) v i).
Proof.
move=>hV;elim=>[|k hPrefix];first by rewrite big_ord0;exact:rectifiable_current_zero.
rewrite big_ord_recr;exact:rectifiable_current_add hPrefix (hV k).
Qed.
End RectifiableCurrentFiniteSums.
