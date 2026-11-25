(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), pp. 333–335:
    return the original functional holomorphic strata
    from invertible linear source coordinates. Their
    actual equations and nonvanishing function pull back;
    the chain rule and surjectivity preserve the
    independence of their actual differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicFiniteCalculus FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP Hom TensorUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness FiniteIndependence NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormOpenDomainLaws NormBoundedLinearTopology
  HolomorphicUP HolomorphicLinear HolomorphicRestriction FunctionalHolomorphicSubmanifoldUP BlockDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_holomorphic_linear_pullback]:
    the functional holomorphic submanifold conclusion of
    3.4.12, p. 339, extending 3.4.8(11), pp. 333–335, is invariant
    under the original orthogonal coordinates. This
    supporting result uses only boundedness and surjectivity
    of the actual linear map, retaining all equations. *)
Theorem functional_holomorphic_linear_pullback (R:realType) n m
    (u:Hom (coordinate_space (ComplexScalars.C R) n) (coordinate_space (ComplexScalars.C R) n)) (U S:set (coordinate_space (ComplexScalars.C R) n)):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
    (restricted_space (ComplexScalars.embed R) (coordinate_space (ComplexScalars.C R) n))
    (@holomorphic_coordinate_norm R n) (@holomorphic_coordinate_norm R n) (complex_hom_real u) ->
  (forall y,exists x,u x = y) ->
  @is_functional_holomorphic_submanifold R n m U S ->
  @is_functional_holomorphic_submanifold R n m (u @^-1` U) (u @^-1` S).
Proof.
move=>hBound hOnto [hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]].
pose X:=coordinate_space (ComplexScalars.C R) n.
pose NX:=@holomorphic_coordinate_norm R n.
pose hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n).
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose A:set X:=u @^-1` U.
have hContinuous:=@norm_bounded_linear_continuous R XR XR NX NX hNX hNX (complex_hom_real u) hBound.
have hA:@open T A:=@open_comp T T u U (fun x _=>hContinuous x) hU.
have hInterior x (hx:A x):@norm_domain_interior R XR NX A x.
  have hOpen:=hA;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R XR NX hNX A x).2 (hOpen x hx).
have hUHolomorphic:=@holomorphic_bounded_linear R X X NX NX hNX hNX A u hInterior hBound.
have hCompose (phi:X->(ComplexScalars.C R)^o):
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) U phi ->
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (fun x=>phi (u x)).
  move=>hPhi;exact:(@holomorphic_compose_on R X X (ComplexScalars.C R)^o NX NX (@complex_modulus R)
    hNX hNX (@complex_modulus_real_norm R) A U u phi (fun x hx=>hx) hUHolomorphic hPhi).
split;first exact:hMN.
split;first exact:hA.
exists (fun i x=>f i (u x)),(fun x=>g (u x));split;first by move=>i;exact:hCompose _ (hF i).
split;first exact:hCompose _ hG.
split;first by move=>x;exact:hEquation (u x).
move=>x hx;have [D [hD hIndependent]]:=hDifferentials (u x) hx.
exists (fun i=>hom_comp (D i) u);split.
- move=>i.
  have hLinear:=@norm_differential_linear R XR XR NX NX hNX hNX A x (complex_hom_real u) (hInterior x ((hEquation (u x)).1 hx).1) hBound.
  have hChain:=norm_differential_chain hNX hNX (@complex_modulus_real_norm R) hLinear (hD i).
  have hSame:(fun y=>A y /\U (u y)) = A.
    apply:funext=>y;apply:propext;split;[by case|by move=>hy;split].
  rewrite hSame in hChain.
  have hComposite:complex_hom_real (hom_comp (D i) u) = hom_comp (complex_hom_real (D i)) (complex_hom_real u).
    by apply:hom_ext=>z.
  rewrite hComposite;exact:hChain.
- pose linearL:=@dual_map (ComplexScalars.C R) X (hom_as_linear u).
  have hValue phi:linearL phi = hom_comp phi u.
    apply:hom_ext=>z;by rewrite /linearL dual_mapE hom_compE hom_as_linearE.
  have hInjective:injective linearL.
    move=>phi psi hEqual;apply:hom_ext=>y.
    have [z <-]:=hOnto y.
    have hAt:=congr1 (fun eta:Hom X (ComplexScalars.C R)^o=>eta z) hEqual.
    by rewrite !hValue !hom_compE in hAt.
  have hMapped:=@finite_independent_map (ComplexScalars.C R) (Finite.clone 'I_(n-m) _) (Hom X (ComplexScalars.C R)^o) (Hom X (ComplexScalars.C R)^o)
    linearL D hInjective hIndependent.
  have hSame:(fun i=>linearL (D i)) = (fun i=>hom_comp (D i) u).
    apply:funext=>i;exact:hValue.
  by rewrite hSame in hMapped.
Qed.
