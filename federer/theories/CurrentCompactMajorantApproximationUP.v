(** Federer (1969), 4.1.14, pp. 371–372: continuous
    Lebesgue-almost-everywhere majorants of the actual differential
    survive smoothing near the compact source. The independent
    specification retains the original partial-D graph and an
    arbitrary open target. Nonnegativity of sigma is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  SmoothCompactSet EuclideanHomOperator CurrentMapDifferential
  EuclideanLebesgueDimensions MeasureAlmostUP CurrentCompactSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCompactMajorantApproximationUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).

(** Source for [is_current_ae_differential_majorant]: the original
    condition ||Df(x)|| <= sigma(x) for Lebesgue almost all x in U,
    Federer 4.1.14, p. 371. Actual differentiability and its bound
    hold on one conull part of U. No arbitrary total extension of
    the partial derivative is used to define this premise. *)
Definition is_current_ae_differential_majorant (U:set X) (f:X->Y)
    (sigma:X->R^o):Prop:=
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set x|U x->exists D:Hom X Y,
      has_norm_differential NX NY U f x D /\ @euclidean_operator_norm R n nu D<=sigma x].

(** Source for [is_current_compact_majorant_smooth_approximation]:
    smoothing commutes with differentiation in Federer 4.1.14,
    p. 371, with the positive error removed in the limit. The
    chosen ordinary bound L may be any finite bound; the new
    pointwise cap is needed only on the original compact K. *)
Record is_current_compact_majorant_smooth_approximation
    (U:set X) (V:set Y) (K:smooth_compact_set hNX U)
    (f:X->Y) (sigma:X->R^o) (Z:set X)
    (g:nat->X->Y) (eta:nat->R):Prop:={
  (** Source: the common-domain smooth approximation of 4.1.14,
      p. 370. Its finite ordinary bound is not required to be optimal. *)
  current_compact_majorant_ordinary:exists L:R,
    @is_current_compact_smooth_approximation R n nu U V K f L Z g;
  (** Source: positive approximation error, used before passing
      to the limit in the weighted inequality of 4.1.14, p. 371. *)
  current_compact_majorant_error_positive:forall i,0<eta i;
  (** Source: the smoothing error tends to zero, supporting the
      original weighted inequalities of 4.1.14, pp. 371–372. *)
  current_compact_majorant_error_zero:forall eps:R,0<eps->exists N:nat,
    forall i:nat,(N<=i)%N->eta i<eps;
  (** Source: the actual differential of the smoothed map is bounded
      by the original continuous sigma plus the vanishing error,
      supporting Federer 4.1.14, pp. 371–372. *)
  current_compact_majorant_differential_bound:forall i x,
    smooth_compact_carrier K x->
    @euclidean_operator_norm R n nu (@current_map_differential R n nu Z (g i) x)
      <=sigma x+eta i
}.
End CurrentCompactMajorantApproximationUP.
