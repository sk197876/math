(** Federer (1969), 3.4.5, p. 321: actual
    analytic pullback of a global vanishing function to
    the homogeneous real cubic cone in the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDiffeomorphismUP NormAnalyticUP NormAnalyticLocal NormAnalyticOperations
  CartanSurfaceUP CartanSurfaceSealed CartanAxisCoordinate CartanNormalizationInverse CartanNormalizationEquation
  CubicConePolynomialDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pullback.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation AN Y NY hNY A f:=(@norm_analytic R X Y NX NY hNX hNY A f).

(** Source for [cartan_cone_pullback_exist]: an original
    global analytic function zero on the actual locally
    analytic surface gives an actual analytic function zero
    on every cone point of the actual inverse-coordinate
    neighbourhood, supporting the example in 3.4.5, p. 321. *)
Theorem cartan_cone_pullback_exist (f:X->R):
  AN R^o N hN setT f ->(forall v,CartanSurface.set v ->f v=0) ->
  exists T G:X->X,exists r:R,
    0<r /\(forall v,NX v<r ->v ord_max<1) /\T 0=0 /\G 0=0 /\
    (forall v,(T v) ord0=v ord0) /\
    (forall v,(T v) (Ordinal (isT:(1<3)%N))=v (Ordinal (isT:(1<3)%N))) /\
    (forall v,(T v) ord_max=cartan_axis_coordinate (v ord_max)) /\
    AN X NX hNX U T /\AN X NX hNX (T @` [set v|NX v<r]) G /\
    is_norm_diffeomorphism hNX hNX [set v|NX v<r] (T @` [set v|NX v<r]) T G 1%N /\
    AN R^o N hN (T @` [set v|NX v<r]) (fun v=>f (G v)) /\
    (T @` [set v|NX v<r]) 0 /\
    forall v,(T @` [set w|NX w<r]) v ->cubic_cone_polynomial_value v=0 ->f (G v)=0.
Proof.
move=>hf hZero.
have [T [G [r [hr [hRU [hT0 [hG0 [hX [hY [hZ [hT [hG hInverse]]]]]]]]]]]]:=
  @cartan_normalization_inverse_exist R.
pose W:=[set v:X|NX v<r].
pose V:=T @` W.
have hF:AN R^o N hN V (fun v=>f (G v)):=
  norm_analytic_compose_on (fun v (_:V v)=>Logic.I) hG hf.
have hW0:W 0 by rewrite /W /= (real_seminorm_zero hNX.1).
have hV0:V 0 by exists 0;first exact:hW0;exact:hT0.
have hCone v (hv:V v) (hCv:cubic_cone_polynomial_value v=0):f (G v)=0.
  have hWG:W (G v):=norm_diffeomorphism_inverse_maps hInverse hv.
  have hCoordinate:T (G v)=v:=norm_diffeomorphism_right_inverse hInverse hv.
  apply:hZero.
  apply:(cartan_normalization_surfaceP hX hY hZ (hRU (G v) hWG)).2.
  by rewrite hCoordinate.
exists T,G,r;split;first exact:hr;split;first exact:hRU.
split;first exact:hT0;split;first exact:hG0.
split;first exact:hX;split;first exact:hY;split;first exact:hZ.
split;first exact:hT;split;first exact:hG;split;first exact:hInverse.
split;first exact:hF;split;first exact:hV0;exact:hCone.
Qed.
End Pullback.
