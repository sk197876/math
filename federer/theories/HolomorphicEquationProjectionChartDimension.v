(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332:
    retain the original ambient dimension n
    in the prescribed projection chart.
    The proved joint-coordinate theorem uses
    the equivalent indexing n=m+(n-m). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import FiniteCoordinates ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicCoordinateNorm Hom RealNormUP NormDifferentialUP NormAnalyticUP NormCoordinateSystemUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex HolomorphicEquationProjectionChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_equation_projection_chart_any_dimension]:
    the original m-dimensional chart in
    R^n, 3.4.12, p. 339, extending 3.4.8(10), pp. 331–332.
    This index connection changes no vector,
    equation, projection or theorem hypothesis. *)
Theorem holomorphic_equation_projection_chart_any_dimension (R:realType) n m (hMN:(m<=n)%N):
  forall (A Z:set (coordinate_space (ComplexScalars.C R) n)) (P:Hom (coordinate_space (ComplexScalars.C R) n) (coordinate_space (ComplexScalars.C R) m))
    (f:'I_(n-m)->coordinate_space (ComplexScalars.C R) n->ComplexScalars.C R) (delta:coordinate_space (ComplexScalars.C R) n->ComplexScalars.C R),
  @norm_bounded_linear R
    (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
    (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) m))
    (@holomorphic_coordinate_norm R n) (@holomorphic_coordinate_norm R m) (complex_hom_real P) ->
  (forall j,@is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o (@holomorphic_coordinate_norm R n)
    (@complex_modulus R) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
    (@complex_modulus_real_norm R) A (f j)) ->
  @is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (ComplexScalars.C R)^o (@holomorphic_coordinate_norm R n)
    (@complex_modulus R) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
    (@complex_modulus_real_norm R) A delta ->
  (forall x,Z x <->A x /\(forall j,f j x = 0) /\delta x<>0) ->
  (forall a,Z a ->exists D:'I_(n-m)->Hom
    (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
    (forall j,@has_norm_differential R
      (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      (@holomorphic_coordinate_norm R n) (@complex_modulus R) A (f j) a (D j)) /\
    forall u,P u = 0 ->(forall j,D j u = 0) ->u=0) ->
  forall a,Z a ->exists (U:set (coordinate_space (ComplexScalars.C R) n)) (V:set (coordinate_space (ComplexScalars.C R) m)) (psi:coordinate_space (ComplexScalars.C R) m->coordinate_space (ComplexScalars.C R) n),
    U a /\(forall x,U x ->A x /\delta x<>0) /\@is_inner_convex R (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) m)) V /\
    @is_holomorphic R (coordinate_space (ComplexScalars.C R) n) (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R n)
      (@holomorphic_coordinate_norm R m) (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
      (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) U P /\
    @is_holomorphic R (coordinate_space (ComplexScalars.C R) m) (coordinate_space (ComplexScalars.C R) n) (@holomorphic_coordinate_norm R m)
      (@holomorphic_coordinate_norm R n) (complex_norm_real (@holomorphic_coordinate_norm_laws R m))
      (complex_norm_real (@holomorphic_coordinate_norm_laws R n)) V psi /\
    is_norm_coordinate_system (complex_norm_real (@holomorphic_coordinate_norm_laws R n))
      (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) Z U V P psi 1%N.
Proof.
have hSize:n=(m+(n-m))%N by rewrite subnKC.
rewrite hSize addKn.
move=>A Z P f delta hP hF hDelta hZ hJoint a ha.
exact:(@holomorphic_equation_projection_chart R m (n-m) A Z P hP f delta hF hDelta hZ hJoint a ha).
Qed.
