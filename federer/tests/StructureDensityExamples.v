(** Federer (1969), 3.3.2, pp. 287–288: concrete
    regressions retain an empty original set, the positive
    R^0 counting atom, and a genuinely infinite atomic mass
    without any local-finiteness hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm FiniteCoordinates EuclideanOneCoordinate
  EuclideanOneNormDifferential AdjointUP Adjoint OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace
  MeasureUP MeasureBasic CountingMeasure WeightedCountingMeasure NonnegativeSum NonnegativeSumSupport
  BorelFunctionUP ExtendedRealOrderTopology StructureConeUP StructureCone
  StructureConeBasic StructureProjectionKernel StructureProjectionCone
  StructureOpenCompactInner StructureOpenFibreMass StructureConeOpen
  StructureConeJointOpen StructureCompactConeContainment
  StructureLimsupLevels StructureBorelOrderCriterion StructureLimsupBorel
  StructureConeDensityUP StructureConeDensity StructureConeCostOpen
  StructureConeDensityReciprocals StructureConeDensityFormula
  StructureConeDensityBorel StructureConeDensityValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_density_empty_source]: actual
    empty-source regression for Federer 3.3.2, p. 287.
    Counting measure satisfies the original closed-set
    hypothesis, and the original cone-density value is zero. *)
Example structure_density_empty_source (R:realType) n m (hmn:(m<=n)%N)
    (delta:R) (z:inner_metric_space (@euclidean_inner_productP R n)*
      euclidean_projection_space R n m):
  0<delta ->structure_cone_density hmn
    (@counting_measure R (inner_metric_space (@euclidean_inner_productP R n)))
    set0 delta z=0%E.
Proof.
move=>hDelta; apply:(@structure_cone_density_constant_cost R n m hmn
  (@counting_measure R (inner_metric_space (@euclidean_inner_productP R n)))
  set0 delta z 0%E hDelta)=>r s _ _.
by rewrite /structure_cone_cost set0I (measure_empty (counting_measure_is_measure R _)) !mul0e.
Qed.

(** Source for [structure_density_positive_zero_ambient_atom]:
    the actual R^0 endpoint of Federer 3.3.2, p. 287.
    Its whole counting mass is one, but every cone excludes
    the sole point, and the original density is zero. *)
Example structure_density_positive_zero_ambient_atom (R:realType)
    (p:euclidean_projection_space R 0 0):
  @counting_measure R (inner_metric_space (@euclidean_inner_productP R 0)) setT= 1%E /\
  structure_cone_density (leqnn 0)
    (@counting_measure R (inner_metric_space (@euclidean_inner_productP R 0)))
    setT 1 (0,p)=0%E.
Proof.
pose E:=inner_metric_space (@euclidean_inner_productP R 0).
have hWhole:(@setT E)=[set (0:E)].
  apply/seteqP; split=>x; last by [].
  move=>_; apply/ffunP=>i; have hi:=ltn_ord i; by rewrite ltn0 in hi.
split.
- rewrite hWhole counting_measure_sum; apply:nonnegative_sum_singleton.
  by rewrite lee_fin.
- apply:(@structure_cone_density_constant_cost R 0 0 (leqnn 0)
    (@counting_measure R E) setT 1 (0,p) 0%E ltr01)=>r s _ _.
  have hCone:structure_cone (structure_projection_kernel (leqnn 0) p) (0:E) r%:E s=set0.
    apply/seteqP; split=>x hx; last by [].
    have hx0:x=(0:E) by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
    subst x; exact:(structure_cone_vertex_excluded hx).
  by rewrite /structure_cone_cost hCone setI0 (measure_empty (counting_measure_is_measure R E)) !mul0e.
Qed.

(** Source for [structure_density_actual_infinite_mass]: an
    actual infinite-mass regression for Federer 3.3.2,
    pp. 287–288. Give every line atom infinite weight,
    take A={1}, base point zero, delta three and the actual
    projection to R^0. The density is infinity and its
    original parameter function is Borel. *)
Example structure_density_actual_infinite_mass (R:realType):
  exists p:euclidean_projection_space R 1 0,
    let E:=inner_metric_space (@euclidean_inner_productP R 1) in
    let mu:=@weighted_counting_measure R E (fun _=>+oo%E) in
    let A:=[set euclidean_one_embed (1:R)] in
    structure_cone_density (leq0n 1) mu A 3 (0,p)=+oo%E /\
    is_borel_function (fun z:E*euclidean_projection_space R 1 0=>
      (structure_cone_density (leq0n 1) mu A 3 z:extended_real_line R)).
Proof.
have [f hf]:=@euclidean_orthogonal_injection_exists R 1 0 (leq0n 1).
have hp:is_orthogonal_projection (@euclidean_inner_product R 1)
    (@euclidean_inner_product R 0)
    (inner_adjoint (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 1) (@coordinate_basisP R 0) f).
  by exists f; split; [exact:hf|exact:inner_adjointP].
pose p:=orthogonal_projection_of (@euclidean_inner_productP R 0)
  (@euclidean_inner_productP R 1) (@coordinate_basisP R 1) hp.
exists p; cbn zeta.
pose E:=inner_metric_space (@euclidean_inner_productP R 1).
pose mu:=@weighted_counting_measure R E (fun _=>+oo%E).
pose A:set E:=[set euclidean_one_embed (1:R)].
have hWeight (x:E):(0<=(+oo: \bar R))%E by exact:leey.
have hMu:is_structure_measure mu.
  split; first exact:(@weighted_counting_measure_is_measure R E (fun _=>+oo%E) hWeight).
  move=>C _; exact:(@weighted_counting_measure_measurable R E (fun _=>+oo%E) C hWeight).
split; last exact:(@structure_cone_density_borel R 1 0 (leq0n 1) mu A 3 hMu).
apply:(@structure_cone_density_infinite_fixed_radius R 1 0 (leq0n 1) mu A 3 2 (0,p)).
- apply/andP; split; [by rewrite ltr0n|by rewrite ltr_nat].
- move=>s hs.
  have hZero x:euclidean_projection_linear p x=0.
    by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
  have hIn:structure_cone (structure_projection_kernel (leq0n 1) p) (0:E) 2%E s
      (euclidean_one_embed (1:R)).
    apply/(structure_projection_coneE (leq0n 1) p 0 2%E s).
    rewrite subr0 hZero inner_norm0 mulr0 euclidean_one_norm_coordinate
      /euclidean_one_embed ffunE normr1; split; first exact:ltr01.
    by rewrite lte_fin ltr1n.
  have hMass:mu (A `&` structure_cone (structure_projection_kernel (leq0n 1) p)
      (0:E) 2%E s)=+oo%E.
    apply/eqP; rewrite eq_le leey /= /mu weighted_counting_measure_sum.
    apply:(nonnegative_sum_term _ (conj (erefl _) hIn)).
  by rewrite /structure_cone_cost hMass !expr0 !mule1.
Qed.
