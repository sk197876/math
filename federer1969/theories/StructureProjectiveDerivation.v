(** Federer (1969), 3.3.4, p. 291: the
    actual projective reference satisfies every
    standing premise of the cited theorem 2.9.17.
    Its density, strict uniform growth and
    centred-ball Vitali relation are proved;
    numerator measures need only be outer measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  StructureProjectiveSpace StructureProjectiveMeasure StructureProjectiveDensity
  StructureProjectiveMeasureInvariant HomogeneousDensityBallGrowth UniformGrowthCenteredVitali
  OrthogonalGroupTopology EuclideanOrthogonalInvariantMeasures
  MeasureUP MeasureBasic MeasureDerivationContext MeasureAlmostUP
  UniformBallGrowthAdequacy CenteredBallRelations UpperBallRatioDichotomy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_derivation_context]:
    all actual reference premises for the
    application of 2.9.17 in Federer 3.3.4,
    p. 291. The radius cutoff and Vitali
    relation are conclusions, with no assumed
    density or supplied regularity constant. *)
Theorem structure_projective_derivation_context (R:realType) m:
  exists d:R,0<d /\ 1<(4:R)*(5:R)^+m /\
    has_uniform_fivefold_ball_growth (@structure_projective_measure R m) setT d ((4:R)*(5:R)^+m) /\
    is_measure_derivation_context (@structure_projective_measure R m)
      (@centered_closed_ball_relation R (structure_projective_space R m)).
Proof.
pose M:=structure_projective_space R m.
pose mu:=@structure_projective_measure R m.
have hDerivation:=@structure_projective_derivation_measure R m.
have hMu:=derivation_measure_law hDerivation.
have hNonempty:exists a:M,True.
  apply:contrapT=>hNo.
  have hEmpty:(@setT M)=set0.
    apply/seteqP; split=>a; last by [].
    move=>_; apply:hNo; by exists a.
  have hPositive:(0<mu setT)%E:=(andP (@structure_projective_measure_positive_finite R m)).1.
  have hZero:mu set0=0%E:=measure_empty hMu.
  by move:hPositive; rewrite hEmpty hZero ltxx.
have [a _]:=hNonempty.
have [mulS [invS [eS hS]]]:=@orthogonal_group_restriction_exists R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1).
have [d [hd [hLambda hGrowth]]]:=@homogeneous_density_one_uniform_growth R M mu m a
  (@structure_projective_closed_ball_mass R m mulS invS eS hS)
  (@structure_projective_density_one R m mulS invS eS hS a).
exists d; split=>//; split=>//; split=>//; constructor=>//.
exact:(uniform_fivefold_growth_centered_vitali hDerivation hd hLambda hGrowth).
Qed.

(** Source for [structure_projective_ratio_dichotomy]:
    the actual application of Federer 2.9.17
    in 3.3.4, p. 291. Every numerator
    outer measure is retained, with no Borel
    regularity or local-finiteness premise on it. *)
Theorem structure_projective_ratio_dichotomy (R:realType) m
    (psi:set (structure_projective_space R m)->\bar R)
    (T:set (structure_projective_space R m)):
  is_measure psi ->measure_measurable (@structure_projective_measure R m) T ->psi T=0%E ->
  measure_almost_everywhere_on (@structure_projective_measure R m) T
    (has_zero_or_infinite_upper_ball_ratio psi (@structure_projective_measure R m)).
Proof.
move=>hPsi hT hNull.
have [d [hd [hLambda [hGrowth hContext]]]]:=@structure_projective_derivation_context R m.
exact:(federer_2_9_17 hContext hPsi hd hGrowth hT hNull).
Qed.
