(** Federer (1969), 3.3.10, p. 296: original first and second
    plane-growth loci are Borel on the actual projection parameters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructurePlaneGrowth StructureProjectionKernel StructurePlaneCostOrder
  StructurePlaneGrowthReciprocals StructurePositiveGrowthLimits StructureConeDensity
  StructureConeDensityBorel StructureBorelValueFibres TopologicalBorel
  PositiveRightOrderLimit PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_zero_growth_borel]: original
    first-alternative locus in the measurability argument of Federer
    3.3.10, p. 296. Nonnegative original radius suprema identify
    ordinary zero limits with zero upper limits, and actual 3.3.2
    applies at each reciprocal cutoff. A remains arbitrary. *)
Theorem structure_projection_zero_growth_borel (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->borel_set
    [set z:inner_metric_space (@euclidean_inner_productP R n)*euclidean_projection_space R n m|
      structure_plane_zero_growth m phi A z.1 (structure_projection_kernel hmn z.2)].
Proof.
move=>hPhi.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=euclidean_projection_space R n m.
have hEquivalent z delta:0<delta ->
    (positive_right_extended_order_limit
      (structure_plane_radial_supremum m phi A z.1 (structure_projection_kernel hmn z.2) delta) 0%E <->
      structure_cone_density hmn phi A delta z=0%E).
  move=>hDelta.
  have hPositive s:0<s ->
      (0<=structure_plane_radial_supremum m phi A z.1 (structure_projection_kernel hmn z.2) delta s)%E.
    move=>hs; exact:(@structure_plane_radial_nonnegative R n (n-m) m phi A z.1
      (structure_projection_kernel hmn z.2) delta s hPhi.1 hDelta hs).
  have hDensity:structure_cone_density hmn phi A delta z=
      positive_radius_upper_limit (structure_plane_radial_supremum m phi A z.1
        (structure_projection_kernel hmn z.2) delta).
    clear hPositive; case:z=>a p; exact:esym (structure_plane_kernel_densityE hmn phi A a p delta).
  rewrite hDensity; split.
  - exact:structure_ordinary_zero_limit_upper hPositive.
  - exact:structure_nonnegative_zero_upper_limit_ordinary hPositive.
have hEqual:[set z:X*P|structure_plane_zero_growth m phi A z.1 (structure_projection_kernel hmn z.2)]=
    \bigcup_i [set z:X*P|structure_cone_density hmn phi A (((i.+1)%:R:R)^-1) z=0%E].
  apply/seteqP; split=>z.
  - move/(@structure_plane_zero_reciprocal_iff R n (n-m) m phi A z.1 (structure_projection_kernel hmn z.2) hPhi.1)=>[i hi].
    exists i=>//; apply/(hEquivalent z _ _); first by rewrite invr_gt0 ltr0n.
    exact:hi.
  - move=>[i _ hi]; apply/(@structure_plane_zero_reciprocal_iff R n (n-m) m phi A z.1 (structure_projection_kernel hmn z.2) hPhi.1).
    exists i; apply/(hEquivalent z _ _); first by rewrite invr_gt0 ltr0n.
    exact:hi.
rewrite hEqual; apply:borel_set_countable_union (countableP setT) _=>i _.
exact:(@structure_borel_value_fibre R [the topologicalType of (X*P)%type]
  (fun z=>structure_cone_density hmn phi A (((i.+1)%:R:R)^-1) z) 0%E
  (@structure_cone_density_borel R n m hmn phi A (((i.+1)%:R:R)^-1) hPhi)).
Qed.

(** Source for [structure_projection_infinite_growth_borel]: original
    second-alternative locus in Federer 3.3.10, p. 296. The
    infinite upper value at every positive original cutoff is an
    exact countable intersection of actual 3.3.2 Borel value fibres. *)
Theorem structure_projection_infinite_growth_borel (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->borel_set
    [set z:inner_metric_space (@euclidean_inner_productP R n)*euclidean_projection_space R n m|
      structure_plane_infinite_growth m phi A z.1 (structure_projection_kernel hmn z.2)].
Proof.
move=>hPhi.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose P:=euclidean_projection_space R n m.
have hEqual:[set z:X*P|structure_plane_infinite_growth m phi A z.1 (structure_projection_kernel hmn z.2)]=
    \bigcap_i [set z:X*P|structure_cone_density hmn phi A (((i.+1)%:R:R)^-1) z=+oo%E].
  apply/seteqP; split=>[[a p]|[a p]].
  - move/(@structure_plane_infinite_reciprocal_iff R n (n-m) m phi A a (structure_projection_kernel hmn p))=>h i _.
    change (structure_cone_density hmn phi A (((i.+1)%:R:R)^-1) (a,p)=+oo%E).
    rewrite -(structure_plane_kernel_densityE hmn phi A a p (((i.+1)%:R:R)^-1)); exact:h i.
  - move=>h; apply/(@structure_plane_infinite_reciprocal_iff R n (n-m) m phi A a (structure_projection_kernel hmn p))=>i.
    rewrite (structure_plane_kernel_densityE hmn phi A a p (((i.+1)%:R:R)^-1)); exact:h i Logic.I.
rewrite hEqual; apply:borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=>i _; exact:(@structure_borel_value_fibre R [the topologicalType of (X*P)%type]
    (fun z=>structure_cone_density hmn phi A (((i.+1)%:R:R)^-1) z) +oo%E
    (@structure_cone_density_borel R n m hmn phi A (((i.+1)%:R:R)^-1) hPhi)).
Qed.
