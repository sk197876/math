(** Federer (1969), corrected 3.4.12, p. 339, extending 3.4.8(11), p. 327,
    with the m=0 proof on p. 333:
    the point difference has one original
    functional stratum and an empty holomorphic
    boundary. The empty boundary germ is
    explicit; it has no original dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP SetGermSealed FiniteHolomorphicVarietyBoundary
  FunctionalHolomorphicPoint HolomorphicFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_point_stratification]:
    the actual one-point decomposition in
    the zero-dimensional base of 3.4.12, p. 339, extending 3.4.8(11),
    p. 333, with the published
    boundary correction at p. 327 line 24. *)
Theorem holomorphic_point_stratification (R:realType) n
    (alpha beta:@set_germ_space
      (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) 0)
    m (U0 S0:set (coordinate_space (ComplexScalars.C R) n)):
  @open (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) U0 ->
  U0 0 ->~S0 0 ->
  @SetGerms.meet (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) alpha (@SetGerms.neg (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) beta) = @set_germ (Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _) (0:coordinate_space (ComplexScalars.C R) n) [set 0] ->
  @is_holomorphic_finite_stratification R n alpha beta m U0 S0 1
    (fun _=>U0) (fun _=>[set 0]) (fun _=>set0).
Proof.
move=>hU hU0 hNotS0 hPoint.
pose T:=Topological.clone (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n))) _.
have hUnion:(\bigcup_(i:'I_1) ([set 0]:set (coordinate_space (ComplexScalars.C R) n))) = [set 0].
  apply/seteqP;split.
  - by move=>x [i _ hx].
  - move=>x hx;by exists ord0.
have hClosed:@closed T [set 0].
  exact:(@compact_closed T _ (@metric_hausdorff R
    (real_norm_metric_space (complex_norm_real (@holomorphic_coordinate_norm_laws R n)))) (@compact_set1 T 0)).
have hClosure:@closure T [set 0] = [set 0]:=esym ((@closure_id T [set 0]).1 hClosed).
constructor.
- move=>i;split;first exact:hU.
  split;[exact:hU0|exact:subset_refl].
- by rewrite hUnion.
- move=>i;exists 0%N;split;first exact:leq0n.
  exact:(functional_holomorphic_point hU hU0).
- move=>i;exact:finite_image _ (@finite_set1 T 0).
- move=>i x -> [hS0|[j hEarlier _]];first exact:hNotS0 hS0.
  by move:hEarlier;rewrite (ord1 i) (ord1 j).
- move=>i x [_ hx];left;by rewrite hClosure in hx.
- move=>i;exact:finite_holomorphic_variety_domain_empty hU.
- move=>i;left;reflexivity.
- by move=>i x hEmpty.
Qed.
