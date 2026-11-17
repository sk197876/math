(** Federer (1969), 3.4.8(8), pp. 329–330:
    original suffix-sphere null sets have
    Haar-null orbit preimages under Q_m.
    The original group topology and Haar
    normalization remain. Reuse the existing
    frame extension, sphere measures and compact
    invariant-orbit measure theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerNormalization InnerMetric
  HilbertFormCompactness LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct
  HomInner HomSpaceTopology OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology TopologicalGroupUP TopologicalProductMaps
  MetricSubsetBackground HaarIntegralUP HausdorffMeasure EulerGamma EulerGammaHalfParameters UnitSphereHaarIntegral
  OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar OrthogonalSuffixFixingTransitivity
  OrdinalCoordinateTail AnalyticSuffixSphereCoordinates CompactRestrictedIsometricOrbitNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SuffixHaar.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation H:=(@analytic_suffix_rotation_group R X B hB n e he m).
Local Notation XT:=(inner_metric_space hB).
Local Notation HT:=(inner_metric_space (hom_inner_productP hB hB he)).
Local Notation F:=(fun (q:H) (x:XT)=>@orthogonal_element_map R X B hB n e he (set_val q) x).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_suffix_sphere_haar_coordinate_null]:
    the actual original V(q)=q(e_m)
    transports suffix-sphere exceptional nullity to
    every original Haar measure on Q_m,
    3.4.8(8), p. 330. All continuity,
    transitivity, positive mass and original
    coordinate equations are proved. *)
Theorem analytic_suffix_sphere_haar_coordinate_null (mu:set H->\bar R) (D:set (R_n R (n-m))):
  is_left_haar_measure mulH mu ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-m))) (n-m-1)
    [set y|inner_norm (@euclidean_inner_productP R (n-m)) y = 1 /\D y] = 0%:E ->
  mu [set q:H|D [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (F q (e m))]] = 0%:E.
Proof.
move=>hMu hNull.
have hPositive:(0<n-m)%N by rewrite subn_gt0;exact:ltn_ord m.
have [P [hCoordinates [hMass hNullTransport]]]:=@analytic_suffix_sphere_coordinate_witnesses
  R X B hB n e he hON omega hDual m hMN hPositive.
pose sphere:=@analytic_suffix_unit_sphere R X B hB n e m.
have hLCH:=@orthogonal_coordinate_fixing_lch R X B hB n e he [set i:'I_n|(i<m)%N]
  mulO invO unitO hO mulH invH unitH hH.
have hCompact:=@orthogonal_coordinate_fixing_compact R X B hB n e he [set i:'I_n|(i<m)%N].
have hContinuous:continuous (fun p:H*XT=>(F p.1 p.2:XT)).
  have hMap:continuous (fun q:H=>(orthogonal_element_map (set_val q):HT)).
    move=>q;exact:(continuous_comp (@set_type_val_continuous O H q)
      (@orthogonal_element_continuous R X B hB n e he (set_val q))).
  have hPair:continuous (fun p:H*XT=>((orthogonal_element_map (set_val p.1),p.2):HT*XT)).
    apply:topological_pair_continuous.
    + move=>p;exact:(continuous_comp (@first_projection_continuous H XT p) (hMap p.1)).
    + exact:second_projection_continuous.
  move=>p;exact:(continuous_comp (hPair p)
    (@hom_evaluation_continuous R X X B B hB hB n e he (orthogonal_element_map (set_val p.1),p.2))).
have hCompatible q r x:F (mulH q r) x = F q (F r x).
  rewrite (subgroup_restriction_mul hH).
  exact:(@orthogonal_element_mulE R X B hB n e he mulO invO unitO hO (set_val q) (set_val r) x).
have hInvariant q x:sphere x ->sphere (F q x).
  move=>[hUnit hHead];split.
  - have hNorm:=@orthogonal_map_norm R X X B B hB hB
      (hom_as_linear (orthogonal_element_map (set_val q))) (orthogonal_element_orthogonal (set_val q)) x.
    rewrite hom_as_linearE in hNorm;by rewrite hNorm hUnit.
  - move=>i hI.
    have hFixed:=((@orthogonal_coordinate_fixing_membership R X B hB n e he
      [set j:'I_n|(j<m)%N] (set_val q)).1 (set_valP q)) i hI.
    rewrite -hFixed (orthogonal_element_inner (set_val q));exact:hHead.
have hTransitive x y:sphere x ->sphere y ->exists q:H,F q x = y.
  move=>[hX hXHead] [hY hYHead].
  have hXX:B x x = 1 by rewrite -(inner_norm_sqr hB) hX expr1n.
  have hYY:B y y = 1 by rewrite -(inner_norm_sqr hB) hY expr1n.
  have [q [hQ hValue]]:=@orthogonal_suffix_fixing_transitive R X B hB n e he hON m hMN
    x y hXX hYY hXHead hYHead.
  exists (exist _ q (mem_set hQ));exact:hValue.
have hDistance q (x y:XT):mdist (F q x:XT) (F q y:XT) = mdist x y.
  rewrite !inner_metric_distanceE.
  have hNorm:=@orthogonal_map_norm R X X B B hB hB
    (hom_as_linear (orthogonal_element_map (set_val q))) (orthogonal_element_orthogonal (set_val q)) (x-y).
  by rewrite hom_as_linearE linearB /= in hNorm.
have hAxis:sphere (e m).
  split;first exact:(@InnerNormalization.orthonormal_norm1 R X B hB [the finType of 'I_n] e hON m).
  move=>i hI;rewrite hON.
  have hDifferent:m!=i by apply/eqP=>hEqual;by rewrite -hEqual ltnn in hI.
  by rewrite (negbTE hDifferent).
have hResult:=@compact_restricted_isometric_orbit_null R H XT mulH invH unitH F hLCH sphere
  (n-m-1)%N (2*(euler_gamma_half R)^+(n-m)/euler_gamma (@positive_dimension_half R (n-m) hPositive))
  mu (e m) hAxis (fun x:XT=>D (P x)) hCompact hContinuous hCompatible hInvariant hTransitive hDistance
  (@unit_sphere_gamma_mass_positive R (n-m) hPositive) hMass hMu (hNullTransport D hNull).
have hValues x:P x = [ffun i=>omega (ordinal_coordinate_tail_index hMN i) x].
  apply/ffunP=>i;rewrite ffunE;exact:hCoordinates.
have hSets:[set q:H|D (P (F q (e m)))] =
    [set q:H|D [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (F q (e m))]].
  apply:funext=>q.
  change (D (P (F q (e m))) = D [ffun i=>omega (ordinal_coordinate_tail_index hMN i) (F q (e m))]).
  by rewrite hValues.
by rewrite -hSets.
Qed.
End SuffixHaar.
