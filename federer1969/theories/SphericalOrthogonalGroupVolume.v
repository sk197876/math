(** Federer (1969), 3.2.48, p. 284: the actual
    group volume equals 2^((N-1)/2) times isotropy
    volume times sphere area. This is the whole-sphere
    instance of the proved arbitrary-set 3.2.47(3). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts UnitSphereSpace RectifiableSetUP
  EuclideanUnitSphereRectifiable RectifiableFiniteHausdorffMass HausdorffMeasure
  SphericalOrthogonalProductAlgebra SphericalProductPreimageImage SphericalFinitePullback
  SphericalOrthogonalMass EuclideanStiefelVolumeDimensions RealPowerHalfNatural.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_orthogonal_group_volume]: the exact
    H^nu(O(N)) normalization in the last display of
    3.2.48, p. 284. Every factor is its original
    actual Hausdorff mass, and ambient dimension one retains
    both sphere atoms and the unit isotropy atom. *)
Theorem spherical_orthogonal_group_volume (R:realType) n (c:R_n R n.+1):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1 ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n.+1*(n.+1-1)%/2)%N
    [set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear g)]=
  ((Num.sqrt (2:R))^+n)%:E*
    @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
      (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) n
      (@euclidean_unit_sphere_set R n.+1))%E.
Proof.
move=>hc.
pose E:=@euclidean_unit_sphere_set R n.+1.
have hSphereRect:@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n.+1)) n E.
  have h:=@euclidean_unit_sphere_rectifiable R n.+1.
  by rewrite subn1 succnK in h.
have hRect:=@rectifiable_hausdorff_measure_rectifiable R n n.+1 E hSphereRect.
have hES:E `<=` @euclidean_unit_sphere_set R n.+1 by move=>a ha.
have hPreRect:=@spherical_finite_rectifiable_pullback R n n c E hc hES hRect.
have hMass:=(@federer_3_2_47_3 R n c E n hc hES hPreRect).2.
have hPre:spherical_orthogonal_preimage c E=
    [set g|is_orthogonal_map (@euclidean_inner_product R n.+1)
      (@euclidean_inner_product R n.+1) (hom_as_linear g)].
  apply/seteqP; split=>g; first by move=>[hg _].
  move=>hg; split; first exact hg.
  change (inner_norm (@euclidean_inner_productP R n.+1) (g c)= 1).
  by rewrite (orthogonal_map_norm (@euclidean_inner_productP R n.+1)
    (@euclidean_inner_productP R n.+1) hg) hc.
rewrite hPre (@real_power_half_natural R 2 n ltac:(by rewrite ltr0n)) in hMass.
rewrite euclidean_skew_dimension_successor addnC.
exact hMass.
Qed.
