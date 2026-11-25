(** Federer (1969), 3.4.8(8), pp. 329–330:
    the original suffix sphere has the
    original Euclidean suffix coordinates and
    Gamma-normalized sphere measure. Reorder the
    two coordinate blocks and apply the
    existing prefix-sphere theorems directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct MetricSubsetBackground
  AnalyticPrefixCoordinatesUP AnalyticPrefixCoordinatesSealed AnalyticPrefixSphereAction
  AnalyticPrefixSphereHausdorffMass AnalyticPrefixSphereNullTransport
  OrdinalCoordinateTail OrdinalSuffixReordering HausdorffMeasure EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_suffix_unit_sphere]: the
    original sphere S perpendicular to the
    first m basis vectors in the
    proof of 3.4.8(8), p. 329.
    Membership uses the original ambient norm
    and the original fixed basis. *)
Definition analytic_suffix_unit_sphere (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) m:set (inner_metric_space hB):=
  [set v|inner_norm hB v = 1 /\forall i:'I_n,(i<m)%N ->B v (e i) = 0].

(** Source for [analytic_suffix_sphere_coordinate_witnesses]:
    the original suffix projection identifies
    S with the unit sphere in R^(n-m),
    3.4.8(8), pp. 329–330. Its positive
    Gamma mass and null-coordinate transport
    follow from the existing prefix results;
    no sphere measure conclusion is assumed. *)
Theorem analytic_suffix_sphere_coordinate_witnesses (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  m (hMN:(m<=n)%N) (hPositive:(0<n-m)%N):
  exists P:Hom X (R_n R (n-m)),
    (forall x i,P x i = omega (ordinal_coordinate_tail_index hMN i) x) /\
    @hausdorff_measure R [the metricType R of metric_subset
      (@analytic_suffix_unit_sphere R X B hB n e m)] (n-m-1) setT =
      (2*(euler_gamma_half R)^+(n-m)/euler_gamma (@positive_dimension_half R (n-m) hPositive))%:E /\
    forall D:set (R_n R (n-m)),
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-m))) (n-m-1)
        [set y|inner_norm (@euclidean_inner_productP R (n-m)) y = 1 /\D y] = 0%:E ->
      @hausdorff_measure R [the metricType R of metric_subset
        (@analytic_suffix_unit_sphere R X B hB n e m)] (n-m-1)
        [set u|D (P (val u))] = 0%:E.
Proof.
pose k:=(n-m)%N.
have [forward [back [hFB [hBF [hTail hHead]]]]]:=ordinal_suffix_reordering_exists hMN.
pose f:=fun i:'I_(k+m)=>e (forward i).
pose covector:=fun i:'I_(k+m)=>omega (forward i).
have hF:is_basis f:=@basis_reindex R (Choice.clone 'I_n _) (Choice.clone 'I_(k+m) _)
  X e he back forward hBF hFB.
have hONF:orthonormal_family B f.
  move=>i j;by rewrite /f hON (inj_eq (can_inj hFB)).
have hDualF i j:covector i (f j) = if i==j then 1 else 0.
  by rewrite /covector /f hDual (inj_eq (can_inj hFB)).
pose hK:=(leq_addr m k).
pose P:=@AnalyticPrefixCoordinates.projection R X (k+m)%N covector k hK.
pose S:=@AnalyticPrefixCoordinates.inclusion R X (k+m)%N f k hK.
have hP:=@AnalyticPrefixCoordinates.projection_laws R X (k+m)%N covector k hK.
have hS:=@AnalyticPrefixCoordinates.inclusion_laws R X (k+m)%N f k hK.
have hSphere:(@analytic_suffix_unit_sphere R X B hB n e m) =
    (@analytic_prefix_unit_sphere R X B hB (k+m)%N f k).
  apply:funext=>x;apply:propext;split.
  - move=>[hUnit hOrthogonal];split;first exact:hUnit.
    move=>j hJ;case:(split_ordP j) hJ=>[i ->|i ->] hJ.
    + have hSmall:(i<k)%N:=ltn_ord i.
      have hFalse:=leq_ltn_trans hJ hSmall;by rewrite ltnn in hFalse.
    + rewrite /f hHead;exact:(@hOrthogonal (widen_ord hMN i) (ltn_ord i)).
  - move=>[hUnit hOrthogonal];split;first exact:hUnit.
    move=>j hJ;pose i:'I_m:=Ordinal hJ.
    have hIndex:widen_ord hMN i = j by apply:val_inj.
    have hValue:=hOrthogonal (rshift k i) (leq_addr (i:nat) k).
    by rewrite /f hHead hIndex in hValue.
exists P;split.
- move=>x i;rewrite hP /covector.
  have hIndex:widen_ord hK i = lshift m i by apply:val_inj.
  by rewrite hIndex hTail.
- split.
  + rewrite hSphere.
    exact:(@analytic_prefix_sphere_hausdorff_mass R X B hB (k+m)%N f hF hONF covector hDualF
      k hK P S hP hS hPositive).
  + move=>D hNull;rewrite hSphere.
    exact:(@analytic_prefix_sphere_coordinate_null R X B hB (k+m)%N f hF hONF covector hDualF
      k hK P S hP hS D hNull).
Qed.
