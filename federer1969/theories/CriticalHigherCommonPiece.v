(** Federer (1969), 3.4.2(7), p. 313: a flat piece for the
    lower class on B is a flat piece for the original higher class. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalFlatPieceRestriction CriticalRelativeClassLaws CriticalSubspaceCoordinates
  CriticalDerivativeFunctions CriticalFiniteDerivativeLimit CriticalOscillationLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_higher_common_flat_piece]: the class
    induction step on B in 3.4.2(7), p. 313. Construct the actual
    derivative functions, apply the same lower-class piece to each,
    and use their bounded orthonormal expansion to obtain the ζ
    limit. Assertion (6) gives the required higher-order η limit.
    The compact pair remains fixed for all original functions. *)
Theorem critical_higher_common_flat_piece (R:realType) m d
    (Z:G (R_n R m) d) mu k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C T G:set (R_n R m)) (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k.+1 (grassmann_val Z) S p g ->
  is_critical_flat_piece hNY Z mu S
    (critical_common_tangent_zero_set hNY (grassmann_val Z) S C k.+1) k T G ->
  is_critical_flat_piece hNY Z mu S C k.+1 T G.
Proof.
move=>hChart [hFamily [hTS [hCompact [hGB hLower]]]].
split;first exact:hFamily.
split;first exact:hTS.
split;first exact:hCompact.
split.
- move=>x hx;split;first exact:(hGB x hx).1.
  exact:(hGB x hx).2.1.
- move=>f hf.
  have [e [heZ [heNorm heCoordinates]]]:=critical_subspace_unit_coordinates Z.
  have [fi [hFi hFormula]]:=@critical_derivative_function_family R m mu k Y NY hNY
    (grassmann_val Z) S C p g f (Finite.clone 'I_d _) e hChart hf heZ.
  have hFiZero i c (hc:G c):fi i c=0:=
    (hFi i).2 c (hGB c hc).2.
  have hLimits i:=hLower (fi i) (hFi i).
  have hZeta:=@critical_finite_derivative_oscillation_limit R m Y NY hNY
    (grassmann_val Z) T G f (Finite.clone 'I_d _) e fi k%:R hFiZero heCoordinates
    (hFormula T hTS) hLimits.
  have hGT:G `<=` T by move=>x hx;exact:(hGB x hx).1.
  have hFT:critical_flat_function_class hNY T (T `&` C) f k.+1:=
    critical_flat_function_source_restriction hTS hf.
  have hFirst:(1<=k.+1)%N by [].
  have hF1:=critical_relative_class_lower hFirst hFT.1.
  have hLambda:(1:R)<=k.+1%:R.
    have hNonnegative:0<=(k%:R:R) by rewrite ler0n.
    rewrite -addn1 natrD natr1;lra.
  have [gamma [hGamma hTFamily]]:=hFamily.
  have hLimit:=@critical_oscillation_zero_limit R m d Z gamma Y NY hNY T G f k.+1%:R
    hTFamily hGT hCompact hF1 hLambda.
  have hExponent:(k.+1%:R:R)-1=k%:R by rewrite -addn1 natrD natr1;lra.
  rewrite hExponent in hLimit.
  exact:(hLimit hZeta).
Qed.
