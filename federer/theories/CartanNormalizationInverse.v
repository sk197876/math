(** Federer (1969), 3.4.5, p. 321: actual
    analytic local inverse for the cubic-cone coordinate change
    in the cited example. All maps are local witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormRegularity
  NormDiffeomorphismUP NormAnalyticUP NormAnalyticLocal CartanAxisCoordinate CartanNormalizationMap
  FiniteAnalyticInverseNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Inverse.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 3)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 3)).
Local Notation U:=([set v:X|v ord_max<1]).
Local Notation AN A f:=(@norm_analytic R X X NX NX hNX hNX A f).

(** Source for [cartan_normalization_inverse_exist]: an actual
    analytic diffeomorphism maps an original ball about zero
    to its actual open image, preserving the first two
    coordinates and normalizing the last. Both origins are
    preserved, supporting the counterexample in 3.4.5, p. 321. *)
Theorem cartan_normalization_inverse_exist:
  exists T G:X->X,exists r:R,
    0<r /\(forall v,NX v<r ->v ord_max<1) /\T 0=0 /\G 0=0 /\
    (forall v,(T v) ord0=v ord0) /\
    (forall v,(T v) (Ordinal (isT:(1<3)%N))=v (Ordinal (isT:(1<3)%N))) /\
    (forall v,(T v) ord_max=cartan_axis_coordinate (v ord_max)) /\
    AN U T /\AN (T @` [set v|NX v<r]) G /\
    is_norm_diffeomorphism hNX hNX [set v|NX v<r] (T @` [set v|NX v<r]) T G 1%N.
Proof.
have [T [L [hT [hT0 [hX [hY [hZ [hL hInjective]]]]]]]]:=@cartan_normalization_map_exist R.
have [D hD]:=(@norm_class_firstP R X X NX NX hNX hNX U T).1
  (norm_analytic_class_all_orders hT 1%N).
have hU0:U 0 by rewrite /= ffunE;exact:ltr01.
have hD0:D 0=L:=norm_differential_unique hNX hNX (norm_class_one_differential hD hU0) hL.
have hDI:injective (D 0) by rewrite hD0.
have [r [hr [hRU [G [hInverse hG]]]]]:=@finite_analytic_inverse_neighbourhood R X
  (@euclidean_inner_product R 3) (@euclidean_inner_productP R 3) hNX 3%N
  (@coordinate_basis R 3) (@coordinate_basisP R 3) U T D 0 hT hD hU0 hDI.
have hBall0:[set v:X|NX (v-0)<r] 0.
  change (is_true (NX (0-0)<r));by rewrite subrr (real_seminorm_zero hNX.1).
have hG0:G 0=0 by rewrite -{1}hT0;exact:(norm_diffeomorphism_left_inverse hInverse hBall0).
exists T,G,r;split;first exact:hr.
split;first by move=>v hv;apply:hRU;rewrite subr0.
split;first exact:hT0;split;first exact:hG0.
split;first exact:hX;split;first exact:hY;split;first exact:hZ;split;first exact:hT.
have hSets:[set v:X|NX (v-0)<r]=[set v:X|NX v<r].
  by apply:funext=>v;rewrite /= subr0.
by rewrite -hSets;split.
Qed.
End Inverse.
