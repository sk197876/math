(** Federer (1969), 3.4.12, p. 339, extending 3.4.7,
    p. 324: the original holomorphic germ has null bad
    directions in any full real coordinate chart. The chart
    retains the actual derivative diagonal; no independent
    polynomial or chosen good direction is a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric SymmetricForms SymmetricFormDual
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermRealCoefficientForms
  HolomorphicGermDiagonalNonzero ComplexPolynomialExceptionalDirections EuclideanLebesgueDimensions HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_coordinate_exceptional_directions_null]:
    the ambient and sphere assertions of complex 3.4.7,
    as prescribed in 3.4.12, p. 339. For the standard
    complex space one takes its paired orthonormal real chart
    of dimension 2n; degree zero and source dimension zero remain. *)
Theorem holomorphic_germ_coordinate_exceptional_directions_null (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    a k (alpha:holomorphic_germ_space hNX a) d
    (L:Hom (R_n R d) (restricted_space (ComplexScalars.embed R) X)):
  (forall x:X,exists v,L v=x) ->@HolomorphicGermJets.value R X NX hNX a k alpha<>0 ->
  let diagonal:=fun v:R_n R d=>@ContinuousMultilinear.evaluation R k
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) [ffun _:'I_k=>L v]
    (@HolomorphicGermJets.value R X NX hNX a k alpha) in
  @euclidean_lebesgue_measure R d [set v|diagonal v=0] = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R d)) (d-1)
    [set v|diagonal v=0 /\inner_norm (@euclidean_inner_productP R d) v= 1] = 0%:E.
Proof.
move=>hSurjective hJet diagonal.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
have [F [hF _]]:=@holomorphic_germ_coefficient_forms_exists R X NX hNX a alpha.
pose G:S_m (R_n R d) CR k:=(k`!)%:R*:(S_m_dual (hom_as_linear L) (F k)).
have hHomogeneous:@is_homogeneous_polynomial R (R_n R d) CR k diagonal.
  exists G=>v.
  rewrite sform_polynomial_diagonal_value /G sform_scaleE scalerA.
  have hFactorial:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite mulVf // scale1r S_m_dualE hF.
  have hTuple:[ffun j:'I_k=>tnth (map_tuple (hom_as_linear L) [tuple v|_<k]) j]=[ffun _:'I_k=>L v].
    by apply/ffunP=>j;rewrite !ffunE tnth_map tnth_mktuple hom_as_linearE.
  by rewrite hTuple.
have [x hx]:=@holomorphic_germ_nonzero_jet_diagonal R X NX hNX a k alpha hJet.
have [v hv]:=hSurjective x.
have hNonzero:exists v,diagonal v<>0.
  exists v;by rewrite /diagonal hv.
exact:complex_polynomial_exceptional_directions_null hHomogeneous hNonzero.
Qed.
