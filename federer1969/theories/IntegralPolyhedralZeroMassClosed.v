(** Federer (1969), 4.1.24, p. 381: the
    original integral polyhedral zero-currents form a
    mass-closed class. The preceding integer mass gap
    makes every sufficiently close polyhedral approximation
    the same current. No finite-mass or representation
    premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassBasic CurrentFiniteMassLinearBound
  CurrentMassZeroDetection SmoothCompactSet PolyhedralCurrentAlgebra
  FiniteIntegerPointMassGap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section IntegralPolyhedralZeroMassClosed.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU 0%N).
Local Notation M:=(@CurrentMass.value R h2 n 0%N U hU).
Local Notation Poly:=(@integral_polyhedral_current_class R h2 n 0%N U hU K).

(** Source for [integral_polyhedral_zero_mass_closed]: every
    mass limit of original fixed-K integral polyhedral
    zero-currents is still in that same class,
    the degree-zero conclusion R_0=P-script_0 of
    4.1.24, p. 381. Negative multiplicities and
    empty compacts remain included. *)
Theorem integral_polyhedral_zero_mass_closed (T:C):
  (forall epsilon:R,0<epsilon->exists Q:C,Poly Q /\(M (T-Q)<epsilon%:E)%E)->
  Poly T.
Proof.
move=>hApprox.
have hQuarter:(0:R)<1/4 by lra.
have[Q0 [hQ0 hError0]]:=hApprox (1/4) hQuarter.
have hEqual:forall epsilon:R,0<epsilon->exists Q:C,
    Q=Q0 /\(M (T-Q)<epsilon%:E)%E.
  move=>epsilon hEpsilon.
  have hDelta:0<Num.min epsilon (1/4) by rewrite lt_min hEpsilon hQuarter.
  have[Q [hQ hError]]:=hApprox (Num.min epsilon (1/4)) hDelta.
  have hPolyDifference:Poly (Q-Q0).
    exact:integral_polyhedral_current_add hQ (integral_polyhedral_current_negate hQ0).
  have hErrorQuarter:(M (T-Q)<=(1/4:R)%:E)%E.
    apply:(le_trans (ltW hError));by rewrite lee_fin ge_min lexx orbT.
  have hNegative:=@current_finite_mass_scale_bound R h2 n 0%N U hU
    (-1) (T-Q) (1/4) hErrorQuarter.
  rewrite scaleN1r opprB normrN normr1 mul1r in hNegative.
  have hDifference:=@current_finite_mass_linear_bound R h2 n 0%N U hU
    1 (Q-T) (T-Q0) (1/4) (1/4) hNegative (ltW hError0).
  rewrite scale1r normr1 mul1r addrA subrK in hDifference.
  have hSmall:(M (Q-Q0)<1)%E.
    apply:(le_lt_trans hDifference);rewrite lte_fin;lra.
  have hZero:=@integral_polyhedral_zero_mass_gap R h2 n U hU K
    (Q-Q0) hPolyDifference hSmall.
  exists Q;split.
  - apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hZero.
  - apply:(lt_le_trans hError);by rewrite lee_fin ge_min lexx.
have hMassZero:M (T-Q0)=0%E.
  apply/eqP;rewrite eq_le;apply/andP;split;last exact:current_mass_nonnegative.
  apply/lee_addgt0Pr=>epsilon hEpsilon;rewrite add0e.
  have[Q [-> hError]]:=hEqual epsilon hEpsilon.
  exact:ltW hError.
have hZero:=@current_mass_zero_implies_zero R h2 n 0%N U hU (T-Q0) hMassZero.
have hT:T=Q0 by apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hZero.
by rewrite hT.
Qed.
End IntegralPolyhedralZeroMassClosed.
