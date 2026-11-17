(** Federer (1969), 3.4.8(10), p. 332:
    the actual original equations have compact
    fibres over compact prefix sets away
    from delta=0. Apply the checked
    coordinate bound and closed-bounded compactness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormClassOneUP NormAnalyticUP
  NormFiniteLinearBound AnalyticPrefixCoordinatesUP OrdinalCoordinateTail
  OriginalPolynomialFibreNormBound NormEquationCompactFibre.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactFibres.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables n m:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Hypothesis hMN:(m<=n)%N.
Local Notation Y:=(R_n R m).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Variable P:Hom X Y.
Hypothesis hP:is_analytic_prefix_projection omega hMN P.
Variable first:'I_(n-m).
Variable k:nat.
Hypothesis hK:(0<k)%N.
Variables U C:set Y.
Variable delta:Y->R.
Variable b0:'I_k->Y->R.
Variable b:'I_(n-m)->'I_k->Y->R.
Variable Z:set X.
Hypothesis hCompact:compact [set y:real_norm_metric_space hNY|C y].
Hypothesis hCU:C `<=` U.
Hypothesis hNonzero:forall y,C y ->delta y!=0.
Hypothesis hDelta:@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U delta.
Hypothesis hB0:forall i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b0 i).
Hypothesis hB:forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b j i).
Variable f:'I_(n-m)->X->R.
Hypothesis hF:forall j,norm_class_zero NX (fun t:R^o=>`|t|) (fun x=>U (P x)) (f j).
Hypothesis hZ:forall x,Z x <->U (P x) /\(forall j,f j x = 0) /\delta (P x)<>0.
Hypothesis hRoot:forall x,Z x ->
  (omega (tail first) x)^+k+\sum_(i<k) b0 i (P x)*(omega (tail first) x)^+(i:nat) = 0.
Hypothesis hRelations:forall x,Z x ->forall j,j!=first ->
  delta (P x)*omega (tail j) x = \sum_(i<k) b j i (P x)*(omega (tail first) x)^+(i:nat).

(** Source for [original_polynomial_compact_fibres]:
    compactness of Z intersect p_m inverse(C),
    3.4.8(10), p. 332. All
    coefficients and equations are the actual
    supplied functions. Boundedness is proved
    from the monic equation; it is
    not a new theorem hypothesis. *)
Theorem original_polynomial_compact_fibres:
  compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
Proof.
have [M [hM hBound]]:=@original_polynomial_fibre_norm_bound R X NX hNX n m e he omega hDual
  hMN P hP first k hK U C delta b0 b Z hCompact hCU hNonzero hDelta hB0 hB hRoot hRelations.
have hPBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY n e he P.
apply:(@norm_equation_compact_fibre R X Y NX NY hNX hNY n e he P U C 'I_(n-m) f delta Z
  hPBound hCompact hCU _ hF hZ _).
- move=>y hy;apply/eqP;exact:hNonzero y hy.
- by exists M.
Qed.
End CompactFibres.
