(** Federer (1969), 4.1.24, p. 382: the integral
    flat size is the infimum of the actual rectifiable
    decomposition costs with exactly the original K.
    Specify its lower-bound and approximation laws before
    proving existence or choosing a value. No attaining
    integral decomposition is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentBoundary CurrentMassSealed
  RectifiableCurrentApproximationUP IntegralCurrentClassesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralFlatSizeUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Next:=(@current_space R h2 n U hU m.+1).
Local Notation Rect:=(fun d=>@is_rectifiable_current_supported_in R h2 n d U hU K).
Local Notation M:=(fun d=>@CurrentMass.value R h2 n d U hU).
Local Notation bd:=(@current_boundary R h2 n m U hU).

(** Source for [is_integral_flat_size]: the literal original
    infimum in 4.1.24, p. 382, on an actual current
    and the original same-K rectifiable pairs. The value
    is a finite nonnegative real; arbitrarily close costs
    are required, but no minimum or homogeneity is asserted. *)
Record is_integral_flat_size (T:C) (a:R):Prop:={
  (** Source: nonnegative costs give nonnegative infimum,
      Federer 4.1.24, p. 382. *)
  integral_flat_size_nonnegative:0<=a;
  (** Source: the infimum is a lower bound of every
      original rectifiable decomposition cost, p. 382. *)
  integral_flat_size_lower:forall (A:C) (S:Next),
    Rect m A->Rect m.+1 S->T=A+bd S->
    (a%:E<=M m A+M m.+1 S)%E;
  (** Source: costs approach the original infimum from
      above; attainment is deferred to 4.2.18, p. 382. *)
  integral_flat_size_approximate:forall epsilon:R,0<epsilon->
    exists A:C,exists S:Next,Rect m A /\Rect m.+1 S /\
      T=A+bd S /\(M m A+M m.+1 S<(a+epsilon)%:E)%E
}.

(** Source for [integral_flat_size_greatest_lower_bound]: the
    approximation property gives exactly the original greatest
    lower bound, supporting 4.1.24, p. 382. This
    uses the specification alone, without selecting a pair. *)
Theorem integral_flat_size_greatest_lower_bound (T:C) a
    (hA:is_integral_flat_size T a) b:
  (forall (A:C) (S:Next),Rect m A->Rect m.+1 S->T=A+bd S->
    (b%:E<=M m A+M m.+1 S)%E)->b<=a.
Proof.
move=>hLower;case:(leP b a)=>// hLess.
have hPositive:0<b-a by rewrite subr_gt0.
have[A [S [hR [hS [hEqual hCost]]]]]:=
  @integral_flat_size_approximate T a hA (b-a) hPositive.
rewrite [a+_]addrC subrK in hCost.
have hBad:=le_lt_trans (hLower A S hR hS hEqual) hCost.
by rewrite ltxx in hBad.
Qed.

(** Source for [integral_flat_size_unique]: the original
    infimum value is unique, Federer 4.1.24, p. 382.
    The proof does not inspect a construction or seal. *)
Theorem integral_flat_size_unique (T:C) a b:
  is_integral_flat_size T a->is_integral_flat_size T b->a=b.
Proof.
move=>hA hB;apply/eqP;rewrite eq_le;apply/andP;split.
- exact:(integral_flat_size_greatest_lower_bound hB (integral_flat_size_lower hA)).
- exact:(integral_flat_size_greatest_lower_bound hA (integral_flat_size_lower hB)).
Qed.
End IntegralFlatSizeUP.
