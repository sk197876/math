(** Federer (1969), 4.1.24, p. 382: the fixed-K
    rectifiable class is closed under actual mass limits.
    Follow the original approximation definition and the
    earlier finite mass triangle bound. This lemma proves
    the closure part of mass completeness; it does not
    assume or claim existence of a mass limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentFiniteMassLinearBound RectifiableCurrentApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RectifiableCurrentMassClosed.
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

(** Source for [rectifiable_current_mass_closed]: the original
    approximation property is closed for the mass distance,
    as used for the asserted mass completeness in
    4.1.24, p. 382. Every chosen approximating current
    and its further polyhedral image retain the same K. *)
Theorem rectifiable_current_mass_closed (T:C):
  (forall epsilon:R,0<epsilon->exists S:C,Rect S /\(M (T-S)<epsilon%:E)%E)->
  Rect T.
Proof.
move=>hClosure epsilon hEpsilon.
pose delta:=epsilon/3.
have hDelta:0<delta by rewrite /delta divr_gt0 //;lra.
have[S [hS hTS]]:=hClosure delta hDelta.
have[Q [hQ hSQ]]:=hS delta hDelta.
exists Q;split;first exact:hQ.
have hSum:=@current_finite_mass_linear_bound R h2 n m U hU 1
  (T-S) (S-Q) delta delta (ltW hTS) (ltW hSQ).
rewrite scale1r normr1 mul1r addrA subrK in hSum.
apply:(le_lt_trans hSum);rewrite lte_fin /delta;lra.
Qed.

(** Source for [rectifiable_current_mass_closure_iff]: the
    original class equals its mass closure, the closure
    ingredient of 4.1.24, p. 382. This still makes
    no unproved mass-limit existence assertion. *)
Theorem rectifiable_current_mass_closure_iff (T:C):
  Rect T<->forall epsilon:R,0<epsilon->exists S:C,
    Rect S /\(M (T-S)<epsilon%:E)%E.
Proof.
split;last exact:rectifiable_current_mass_closed.
move=>hT epsilon hEpsilon;exists T;split;first exact:hT.
by rewrite subrr current_mass_zero lte_fin.
Qed.
End RectifiableCurrentMassClosed.
