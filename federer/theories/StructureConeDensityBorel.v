(** Federer (1969), 3.3.2, pp. 287–288: Borel
    measurability of the actual cone-density upper limit. Use
    the published corrected countable formula, with no regularity
    assumption on the original subset A. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  BorelFunctionUP ExtendedRealOrderTopology PositiveRadiusLimits
  StructureConeUP StructureConeDensityUP StructureConeDensity
  StructureConeCostOpen StructureLimsupBorel StructureConeDensityReciprocals
  StructureConeDensityFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_cone_density_borel]: the whole
    assertion of Federer 3.3.2, pp. 287–288, for the
    independently specified sealed upper limit. Only the
    standing closed-set measurability is used. The published
    erratum pp. 5–6, book p. 288 lines 1–6, supplies
    the corrected strict-superlevel countable formula. *)
Theorem structure_cone_density_borel (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R):
  is_structure_measure phi ->
  is_borel_function (fun z:inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m=>
    (structure_cone_density hmn phi A delta z:extended_real_line R)).
Proof.
move=>hPhi.
have he:(fun z=>structure_cone_density hmn phi A delta z)=
    (fun z=>StructureLimsupLevels.structure_tail_upper_limit
      (structure_cone_cost hmn phi A) delta z).
  apply:funext=>z; exact:(structure_cone_density_reciprocalE hmn phi A delta z).
rewrite he; apply:structure_tail_upper_limit_borel=>r s hr hs b.
exact:(@structure_cone_cost_superlevel_open R n m hmn phi A r s b hPhi hr hs).
Qed.

(** Source for [federer_3_3_2]: the literal statement of
    Federer 3.3.2, p. 287: for arbitrary A and delta>0,
    (a,p) maps to the limsup as s tends to zero from above
    of sup_(0<r<delta) phi[A intersect X(a,r,ker p,s)]
    r^(-m)s^(-m), and this extended-valued function is Borel.
    All original hypotheses are retained; the proof uses the
    published correction on p. 288 rather than its uncorrected
    strict-superlevel intersection. *)
Theorem federer_3_3_2 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (delta:R):
  is_structure_measure phi ->0<delta ->
  is_borel_function (fun z:inner_metric_space (@euclidean_inner_productP R n)*
    euclidean_projection_space R n m=>
    (positive_radius_upper_limit (structure_cone_radial_supremum hmn phi A delta z)
      :extended_real_line R)).
Proof.
move=>hPhi _.
have he:(fun z=>positive_radius_upper_limit
    (structure_cone_radial_supremum hmn phi A delta z))=
    (fun z=>structure_cone_density hmn phi A delta z).
  apply:funext=>z; exact:esym (structure_cone_density_bookE hmn phi A delta z).
rewrite he; exact:(@structure_cone_density_borel R n m hmn phi A delta hPhi).
Qed.
