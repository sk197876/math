(** Federer (1969), 3.4.8(11), pp. 333–335:
    return the original functional analytic strata
    from invertible linear source coordinates. Their
    actual equations and nonvanishing function pull back;
    the chain rule and surjectivity preserve the
    independence of their actual differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness FiniteIndependence NormDifferentialUP NormDifferentialLinear
  NormDifferentialChain NormDifferentialLocal NormOpenDomainLaws NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticLinear NormAnalyticOperations FunctionalAnalyticSubmanifoldUP BlockDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_linear_pullback]:
    the functional analytic submanifold conclusion of
    3.4.8(11), pp. 333–335, is invariant
    under the original orthogonal coordinates. This
    supporting result uses only boundedness and surjectivity
    of the actual linear map, retaining all equations. *)
Theorem functional_analytic_linear_pullback (R:realType) n m
    (u:Hom (R_n R n) (R_n R n)) (U S:set (R_n R n)):
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) u ->
  (forall y,exists x,u x = y) ->
  @is_functional_analytic_submanifold R n m U S ->
  @is_functional_analytic_submanifold R n m (u @^-1` U) (u @^-1` S).
Proof.
move=>hBound hOnto [hMN [hU [f [g [hF [hG [hEquation hDifferentials]]]]]]].
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose A:set X:=u @^-1` U.
have hContinuous:=@norm_bounded_linear_continuous R X X NX NX hNX hNX u hBound.
have hA:@open T A:=@open_comp T T u U (fun x _=>hContinuous x) hU.
have hInterior x (hx:A x):norm_domain_interior NX A x.
  have hOpen:=hA;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX A x).2 (hOpen x hx).
have hUAnalytic:=@norm_bounded_linear_analytic R X X NX NX hNX hNX A hInterior u hBound.
have hCompose (phi:X->R^o):
    @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) U phi ->
    @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A (fun x=>phi (u x)).
  move=>hPhi;exact:(@norm_analytic_compose_on R X X R^o NX NX (fun z:R^o=>`|z|)
    hNX hNX (@scalar_absolute_value_norm R) A U u phi (fun x hx=>hx) hUAnalytic hPhi).
split;first exact:hMN.
split;first exact:hA.
exists (fun i x=>f i (u x)),(fun x=>g (u x));split;first by move=>i;exact:hCompose _ (hF i).
split;first exact:hCompose _ hG.
split;first by move=>x;exact:hEquation (u x).
move=>x hx;have [D [hD hIndependent]]:=hDifferentials (u x) hx.
exists (fun i=>hom_comp (D i) u);split.
- move=>i.
  have hLinear:=@norm_differential_linear R X X NX NX hNX hNX A x u (hInterior x ((hEquation (u x)).1 hx).1) hBound.
  have hChain:=norm_differential_chain hNX hNX (@scalar_absolute_value_norm R) hLinear (hD i).
  have hSame:(fun y=>A y /\U (u y)) = A.
    apply:funext=>y;apply:propext;split;[by case|by move=>hy;split].
  by rewrite hSame in hChain.
- pose linearL:=@dual_map R X (hom_as_linear u).
  have hValue phi:linearL phi = hom_comp phi u.
    apply:hom_ext=>z;by rewrite /linearL dual_mapE hom_compE hom_as_linearE.
  have hInjective:injective linearL.
    move=>phi psi hEqual;apply:hom_ext=>y.
    have [z <-]:=hOnto y.
    have hAt:=congr1 (fun eta:Hom X R^o=>eta z) hEqual.
    by rewrite !hValue !hom_compE in hAt.
  have hMapped:=@finite_independent_map R (Finite.clone 'I_(n-m) _) (Hom X R^o) (Hom X R^o)
    linearL D hInjective hIndependent.
  have hSame:(fun i=>linearL (D i)) = (fun i=>hom_comp (D i) u).
    apply:funext=>i;exact:hValue.
  by rewrite hSame in hMapped.
Qed.
