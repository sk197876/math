(** Federer (1969), 4.1.15, p. 372: two original
    smooth approximations have equal values near the coincidence
    set. This independent specification retains the original
    compact K, one open source neighbourhood, both K-only
    approximation laws of 4.1.14 and a neighbourhood that
    may vary with the approximation index. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentLipschitzCompactImage CurrentSmoothApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSupportSmoothComparisonUP.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Variable K:smooth_compact_set hNX U.
Variables f g:X->Y.
Variable A:set X.
Variable Z:set X.
Variables a b:nat->X->Y.

(** Source for [is_current_support_smooth_comparison]: the
    two smoothings used in the conclusion of Federer
    4.1.15, p. 372. Existence is proved separately;
    equality on A never requires equality on all K. *)
Record is_current_support_smooth_comparison:Prop:={
  (** Source for [support_smooth_comparison_open]: the original
      common open source for smoothing, Federer 4.1.15, p. 372. *)
  support_smooth_comparison_open:forall x,Z x->norm_domain_interior NX Z x;
  (** Source for [support_smooth_comparison_source]: this source
      lies in the original U, Federer 4.1.15, p. 372. *)
  support_smooth_comparison_source:Z `<=` U;
  (** Source for [support_smooth_comparison_contains]: smoothing
      is performed near the whole original compact K,
      Federer 4.1.15, p. 372. *)
  support_smooth_comparison_contains:smooth_compact_carrier K `<=` Z;
  (** Source for [support_smooth_comparison_first]: the first
      original smooth family tends uniformly to f on K,
      with one K-only derivative cap, 4.1.15, p. 372. *)
  support_smooth_comparison_first:
    @is_current_smooth_approximation R n nu Z V
      (@current_compact_index_in_open R n U Z K support_smooth_comparison_contains) f a;
  (** Source for [support_smooth_comparison_second]: the second
      original smooth family tends uniformly to g on K,
      with one K-only derivative cap, 4.1.15, p. 372. *)
  support_smooth_comparison_second:
    @is_current_smooth_approximation R n nu Z V
      (@current_compact_index_in_open R n U Z K support_smooth_comparison_contains) g b;
  (** Source for [support_smooth_comparison_neighbourhood]: each
      smooth pair agrees near A, the support locus used
      in the final sentence of 4.1.15, p. 372. *)
  support_smooth_comparison_neighbourhood:forall i,exists W:set X,
    (forall x,W x->norm_domain_interior NX W x) /\
    W `<=` Z /\ A `<=` W /\forall x,W x->a i x=b i x
}.
End CurrentSupportSmoothComparisonUP.
