(** Federer (1969), 3.4.2(9), p. 316: the derivative
    functions on the lower-class flat pieces give higher-order
    flatness of the original function. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP RelativeClassUP
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalRelativeClassLaws CriticalSubspaceCoordinates CriticalTangentDerivativeFunctions
  CriticalFiniteDerivativeLimit CriticalOscillationLimit CriticalOscillation PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_tangent_piece_oscillation_limit]: the
    application of (7) to all actual derivative functions and
    then (6), in the proof of 3.4.2(9), p. 316.
    The original f need not vanish on C. A single lower-class
    pair controls every derivative function, hence the genuine
    relative derivative on T, and gives eta of order k+1
    tending to zero on its original compact G. *)
Theorem critical_tangent_piece_oscillation_limit (R:realType) m d
    (Z:G (R_n R m) d) mu k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C T G:set (R_n R m)) (p:euclidean_projection_space R m mu) g (f:R_n R m->Y):
  is_critical_manifold_chart k.+1 (grassmann_val Z) S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f k.+1 ->
  C `<=` critical_tangent_zero_locus hNY (grassmann_val Z) S f ->
  is_critical_flat_piece hNY Z mu S C k T G ->
  positive_right_extended_order_limit
    (fun delta=>critical_eta NY (grassmann_val Z) T G f k.+1%:R delta) 0%E.
Proof.
move=>hChart hf hCritical [hFamily [hTS [hCompact [hGC hLower]]]].
have [e [heZ [heNorm heCoordinates]]]:=critical_subspace_unit_coordinates Z.
have [fi [hFi hFormula]]:=@critical_tangent_derivative_function_family R m mu k Y NY hNY
  (grassmann_val Z) S C p g f (Finite.clone 'I_d _) e hChart hf hCritical heZ.
have hFiZero i c (hc:G c):fi i c=0:=(hFi i).2 c (hGC c hc).2.
have hLimits i:=hLower (fi i) (hFi i).
have hZeta:=@critical_finite_derivative_oscillation_limit R m Y NY hNY
  (grassmann_val Z) T G f (Finite.clone 'I_d _) e fi k%:R hFiZero heCoordinates
  (hFormula T hTS) hLimits.
have hGT:G `<=` T by move=>x hx;exact:(hGC x hx).1.
have hFirst:(1<=k.+1)%N by [].
have hF1S:=critical_relative_class_lower hFirst hf.
have hF1T:norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY T T f 1.
  move=>x hx;have [U [F [hxU [hF hAgree]]]]:=hF1S x (hTS x hx).
  exists U,F;split;first exact:hxU.
  split;first exact:hF.
  move=>y hy hyU;split;first exact:hy.
  exact:(hAgree y (hTS y hy) hyU).2.
have hLambda:(1:R)<=k.+1%:R.
  have hNonnegative:0<=(k%:R:R) by rewrite ler0n.
  rewrite -addn1 natrD natr1;lra.
have [gamma [hGamma hTFamily]]:=hFamily.
have hLimit:=@critical_oscillation_zero_limit R m d Z gamma Y NY hNY T G f k.+1%:R
  hTFamily hGT hCompact hF1T hLambda.
have hExponent:(k.+1%:R:R)-1=k%:R by rewrite -addn1 natrD natr1;lra.
rewrite hExponent in hLimit;exact:hLimit hZeta.
Qed.
