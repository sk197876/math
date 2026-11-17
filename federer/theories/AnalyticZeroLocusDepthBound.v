(** Federer (1969), 3.4.10, p. 338:
    a nonzero global analytic equation bounds
    the local dimension of its actual zero set
    below the ambient dimension. Reuse the proved
    nonzero-proper-ideal depth bound of 3.4.8. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness
  NormAnalyticUP AnalyticSourceTranslation AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRing AnalyticGermRingLaws LocalGermUP LocalGermSealed SetGermUP
  CommutativeIdealUP GermVanishingSealed GermVanishingRepresentative GermVanishingIdeal
  AnalyticNonzeroIdealDepth AnalyticGlobalNonzeroGerm AnalyticSetLocalDepth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_locus_local_depth_lt]: the
    actual equation bounds every nonempty local
    dimension in the example cited by 3.4.10,
    p. 338. The original opaque depth
    is used; global nonvanishing is proved
    by one actual function value, not by
    assuming a local dimension conclusion. *)
Theorem analytic_zero_locus_local_depth_lt (R:realType) n
    (S:set (R_n R n.+1)) (f:R_n R n.+1->R):
  let X:=R_n R n.+1 in
  let hB:=@euclidean_inner_productP R n.+1 in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) setT f ->
  (exists b,f b<>0) ->(forall x,S x ->f x=0) ->
  forall a,S a ->(@analytic_set_local_depth R n.+1 S a<n.+1)%N.
Proof.
move=>X hB NX hNX hF [b hb] hZero a haS.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose A:set X:=[set x|S (a+x)].
pose q:=fun x:X=>f (a+x).
have hQ:@norm_analytic R X R^o NX (fun t=>`|t|) hNX
    (@scalar_absolute_value_norm R) setT q.
  exact:(@norm_analytic_source_translation R X R^o NX (fun t=>`|t|) hNX
    (@scalar_absolute_value_norm R) setT f a hF).
pose p:@analytic_representative_type R X NX hNX 0:=exist _ q (hQ 0 Logic.I).
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose I:set G:=@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 A).
have hNonzero:analytic_germ p<>@analytic_germ_zero R X NX hNX 0.
  apply:(@analytic_global_nonzero_germ R X NX hNX 0 p hQ).
  exists (b-a);change (f (a+(b-a))<>0);by rewrite addrC subrK.
have hMember:I (analytic_germ p).
  apply/(analytic_set_ideal_representative_equation p A).
  exists setT;split;first exact:openT.
  split;first exact:Logic.I.
  move=>x hx _;exact:hZero (a+x) hx.
have hProper:~I 1.
  move=>hOne.
  change (I (analytic_germ (@analytic_constant_representative R X NX hNX 0 1))) in hOne.
  have [V [hV [hV0 hVanish]]]:=(analytic_set_ideal_representative_equation
    (@analytic_constant_representative R X NX hNX 0 1) A).1 hOne.
  have hA0:A 0 by change (S (a+0));rewrite addr0.
  have hContradiction:(1:R)=0:=hVanish 0 hA0 hV0.
  by move/eqP:hContradiction;rewrite oner_eq0.
have hDual i j:dual_basis (@coordinate_basisP R n.+1) i (@coordinate_basis R n.+1 j)=
    if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
exact:(@analytic_nonzero_proper_ideal_depth_lt R X (@euclidean_inner_product R n.+1)
  hB n (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
  (@euclidean_coordinate_orthonormal_family R n.+1) (dual_basis (@coordinate_basisP R n.+1))
  hDual I (@analytic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0 A))
  hProper (ex_intro _ (analytic_germ p) (conj hMember hNonzero))).
Qed.
