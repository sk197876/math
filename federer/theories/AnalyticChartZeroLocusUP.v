(** Federer (1969), 3.2.33, p. 270: local analytic
    zero tests for intrinsic differential rank. Coordinate
    values may vary; their actual zero locus is intrinsic. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP InnerConvex NormCoordinateSystemUP NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [is_analytic_chart_zero_locus]: the zero tests
    h_(mu+1)=0 underlying the analytic rank-set alternative
    in Federer 3.2.33, p. 270. Independent laws
    specify local actual coordinate systems and analytic scalar
    equations. They assert neither a null-set dichotomy nor
    existence of a zero test, which must be proved. *)
Record is_analytic_chart_zero_locus (R:realType) n m
    (W P:set (R_n R n)):Prop:={
  (** Source for [analytic_chart_zero_locus_subset]: the intrinsic
      rank locus lies in W, Federer 3.2.33, p. 270. *)
  analytic_chart_zero_locus_subset:P `<=` W;
  (** Source for [analytic_chart_zero_locus_coordinates]: local
      analytic equations in actual convex coordinates for the
      rank locus, Federer 3.2.33, p. 270, using
      3.1.19(4), 3.1.22 and 3.1.24, pp. 231,235,240. *)
  analytic_chart_zero_locus_coordinates:forall a,W a ->
    exists (T:set (R_n R n)) (V:set (R_n R m))
      (phi:R_n R n->R_n R m) (psi:R_n R m->R_n R n) (h:R_n R m->R),
      T a /\is_inner_convex V /\
      is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) W T V phi psi 1%N /\
      @norm_analytic R (R_n R m) R^o (inner_norm (@euclidean_inner_productP R m))
        (fun t:R^o=>`|t|) (inner_norm_real_norm (@euclidean_inner_productP R m))
        (@scalar_absolute_value_norm R) V h /\
      forall x,W x ->T x ->(P x <->h (phi x)= 0)
}.
