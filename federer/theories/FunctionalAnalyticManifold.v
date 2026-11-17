(** Federer (1969), 3.4.5, p. 321, used in
    3.4.8(12), pp. 327, 335: a functional analytic
    submanifold has the analytic charts of 3.1.24,
    p. 240. Reuse the proved regular-level theorem,
    openness of rank thresholds, and original biorthogonal vectors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormDifferentialFiniteCalculus NormDifferentialLocal NormDifferentialDirectional
  NormFiniteLinearBound NormClassOneUP NormClassOneRestriction NormRegularity
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormBoundedLinearTopology
  NormClassZeroNonzeroLocus NormLinearDomainLaws NormOpenDomainLaws
  LinearRankUP LinearRankAtLeast LinearSurjectiveRank RankThresholdOpen
  AnalyticSubmanifoldUP AnalyticSubmanifoldChartsUP AnalyticLevelStraightening
  EuclideanScalarAssemblyAnalytic IndependentCoordinateSurjection FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_submanifold_analytic]: original
    independent defining equations, 3.4.5, p. 321,
    give the analytic submanifold charts used in
    3.4.8(12), pp. 327, 335. No constant-rank
    neighbourhood or chart is added as a hypothesis. *)
Theorem functional_analytic_submanifold_analytic (R:realType) n m
    (U S:set (R_n R n)):
  @is_functional_analytic_submanifold R n m U S ->
  @is_euclidean_analytic_submanifold R n m S.
Proof.
move=>[hmn [hU [f [g [hF [hG [hEquation hIndependent]]]]]]].
pose X:=R_n R n.
pose q:=(n-m)%N.
pose Y:=R_n R q.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R q).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R q).
have hOpen x (hx:U x):norm_domain_interior NX U x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U x).2.
  by move:hU;rewrite openE=>h;exact:h x hx.
pose F:X->Y:=fun x=>[ffun i=>f i x].
have hAnalytic:=@euclidean_scalar_assembly_analytic R X NX hNX U q f hOpen hF.
have [D hD]:=(norm_class_firstP hNX hNY U F).1 (norm_analytic_class_all_orders hAnalytic 1%N).
have hSurjective b (hb:S b):forall y,exists x,D b x=y.
  have hbU:U b:=((hEquation b).1 hb).1.
  have [E [hE hEI]]:=hIndependent b hb.
  apply:(@independent_coordinate_surjection R X q E (D b) hEI)=>v i.
  have hLinear:linear (fun y:Y=>(y i:R^o)) by move=>a x y;rewrite !ffunE.
  pose w:=@HomMap R Y R^o (fun y=>(y i:R^o)) (introT (asboolP _) hLinear).
  have hBound:=@norm_finite_linear_bounded R Y R^o NY (fun t:R^o=>`|t|)
    hNY (@scalar_absolute_value_norm R) q (@coordinate_basis R q) (@coordinate_basisP R q) w.
  have hComposite:=@norm_differential_postcompose R X Y R^o NX NY (fun t:R^o=>`|t|)
    hNX U F b (D b) w (norm_class_one_differential hD hbU) hBound.
  have hScalar:has_norm_differential NX (fun t:R^o=>`|t|) U (f i) b (hom_comp w (D b)).
    apply:(@norm_differential_domain_agreement R X R^o NX (fun t:R^o=>`|t|)
      hNX U (fun x=>w (F x)) (f i) b (hom_comp w (D b)) _ hComposite)=>x hx.
    by change ([ffun j=>f j x] i=f i x);rewrite ffunE.
  have hSame:=norm_differential_unique hNX (@scalar_absolute_value_norm R) hScalar (hE i).
  have hEval:=congr1 (fun L:Hom X R^o=>L v) hSame.
  change (D b v i=E i v) in hEval.
  exact:hEval.
apply:(@analytic_regular_level_charts_submanifold R n m S)=>b hb.
have [hbU [hbF hbG]]:=(hEquation b).1 hb.
have hThreshold:=@linear_surjective_rank_at_least R X Y q (@coordinate_basis R q)
  (@coordinate_basisP R q) (D b) (hSurjective b hb).
pose T:set X:=fun x=>U x /\linear_rank_at_least (D x) q.
have hT x (hx:T x):norm_domain_interior NX T x.
  exact:(@rank_threshold_interior R X Y NX (@euclidean_inner_product R n)
    (@euclidean_inner_product R q) (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R q) n (@coordinate_basis R n) (@coordinate_basisP R n)
    erefl U D hOpen (norm_class_one_continuity hD) x q hx.1 hx.2).
have hNonzero:=@norm_class_zero_nonzero_locus_open R X R^o NX (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) U g
  (norm_class_continuous (norm_analytic_class_all_orders hG 0%N)).
pose V:set X:=fun x=>T x /\(U x /\g x!=0).
have hV x (hx:V x):norm_domain_interior NX V x.
  apply:(@norm_domain_intersection_interior R X NX T (fun x=>U x /\g x!=0) x (hT x hx.1)).
  apply:(@norm_domain_interior_neighbourhood R X NX hNX (fun x=>U x /\g x!=0) x).2.
  by move:hNonzero;rewrite openE=>h;exact:h x hx.2.
have hbV:V b by split;[split|split]=>//;apply/eqP.
have hFV:=@norm_analytic_open_restriction R X Y NX NY hNX hNY U V F
  (fun x hx=>hx.1.1) hV hAnalytic.
have hDV:=@norm_class_one_field_open_restriction R X Y NX NY U V F D
  (fun x hx=>hx.1.1) hV hD.
exists q,V,F,D;split;first exact:hV b hbV.
split;first exact:hmn.
split;first exact:leqnn.
split;first exact:hFV.
split;first exact:hDV.
split.
- apply/seteqP;split.
  + move=>x [hx hxV];split;first exact:hxV.
    apply/ffunP=>i;rewrite /F !ffunE ((hEquation x).1 hx).2.1 hbF;reflexivity.
  + move=>x [hxV hEqual];split;last exact:hxV.
    apply/(hEquation x).2;split;first exact:hxV.1.1.
    split;last by apply/eqP;exact:hxV.2.2.
    move=>i;have hCoord:=congr1 (fun y:Y=>y i) hEqual.
    move:hCoord;rewrite /F !ffunE hbF;by move=>->.
- move=>x hx;exact:(@linear_rank_from_full_threshold R X Y q (@coordinate_basis R q)
    (@coordinate_basisP R q) (D x) hx.1.2).
Qed.
