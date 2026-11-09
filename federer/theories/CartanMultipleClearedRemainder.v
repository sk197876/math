(** Federer (1969), 3.4.5, p. 321: the
    original actual finite cleared remainder vanishes for
    every analytic multiple of the adapted surface equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormAnalyticUP FlatExponentialSealed CartanSurfaceEquation CartanCoordinateGeometry
  AnalyticDirectionalCoefficient CartanAnalyticMultipleCoefficients PairedParityCoefficientShift
  ClearedQuadraticSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ClearedRemainder.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation AN f:=(@norm_analytic R X R^o NX N hNX hN U f).
Local Notation Coefficient:=(@is_analytic_directional_coefficient R X R^o NX N hNX hN).

(** Source for [cartan_multiple_cleared_remainder_zero]: every
    actual analytic surface-equation multiple has zero original
    finite cleared remainder at each original nonzero axis
    coordinate below one, supporting 3.4.5, p. 321.
    Actual derivative equations and finite algebra discharge all premises. *)
Theorem cartan_multiple_cleared_remainder_zero (q:X->R) (C E:nat->X->R)
    (P H:nat->nat->X->R) (parity order:nat) (z:R):
  AN q ->(forall r,Coefficient U q r (@coordinate_basis R 3 ord0) (C r)) ->
  (forall r s,Coefficient U (C r) s (@coordinate_basis R 3 j) (P r s)) ->
  (forall r,Coefficient U (fun v=>q v*cartan_surface_equation v) r (@coordinate_basis R 3 ord0) (E r)) ->
  (forall r s,Coefficient U (E r) s (@coordinate_basis R 3 j) (H r s)) ->
  (parity=0%N \/parity= 1%N) ->z<1 ->z!=0 ->
  quadratic_cleared_remainder parity order z (FlatExponential.value (1-z))
    (fun i k=>H i (2*k+parity)%N (cartan_axis_point z))=0.
Proof.
move=>hq hC hP hE hH hParity hz hNonzero.
pose b:=fun i k=>P i (2*k+parity)%N (cartan_axis_point z).
have hArray (i k:nat):H i (2*k+parity)%N (cartan_axis_point z)=
    z*(if (2<=i)%N then b (i-2)%N k else 0)+
    z*(if (1<=k)%N then b i (k-1)%N else 0)-
    FlatExponential.value (1-z)*(if (3<=i)%N then b (i-3)%N k else 0).
  have hOriginal:=@cartan_analytic_multiple_coefficient R q C P i (2*k+parity)%N (E i)
    (H i (2*k+parity)%N) z hq hC hP (hE i) (hH i (2*k+parity)%N) hz.
  rewrite (@paired_parity_coefficient_shift R^o (fun s=>P i s (cartan_axis_point z)) parity k hParity) in hOriginal.
  exact:hOriginal.
have hArrays:(fun i k=>H i (2*k+parity)%N (cartan_axis_point z))=
    (fun i k=>z*(if (2<=i)%N then b (i-2)%N k else 0)+
      z*(if (1<=k)%N then b i (k-1)%N else 0)-
      FlatExponential.value (1-z)*(if (3<=i)%N then b (i-3)%N k else 0)).
  by apply:funext=>i;apply:funext=>k;exact:hArray.
rewrite hArrays.
exact:(@quadratic_cleared_remainder_multiple R (@pchar_num R) parity order z
  (FlatExponential.value (1-z)) b hNonzero).
Qed.
End ClearedRemainder.
