(** Federer (1969), 3.2.47(3), p. 283: the
    exact mass formula for a finite original E, the
    full r=0 boundary. Whole fibres are pairwise disjoint,
    compact and isometric with I. Finite additivity therefore
    proves the original measure identity, including positive
    atoms and empty E. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  finmap classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts SphericalOrthogonalProductAlgebra
  SphericalProductPreimageImage SphericalOrbitCompactness SphericalOrthogonalFibreIsometry
  UnitSphereSpace HausdorffMeasure HausdorffCountingMeasure CountingMeasure
  HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureFiniteAdditivity
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_finite_base_mass]: the exact
    r=0 identity in 3.2.47(3), p. 283, for
    any actual unit c and every finite original sphere
    subset E. No positive-dimensional fibre is discarded. *)
Theorem spherical_finite_base_mass (R:realType) n (c:R_n R n.+1) (E:set (R_n R n.+1)):
  inner_norm (@euclidean_inner_productP R n.+1) c= 1%R ->
  E `<=` @euclidean_unit_sphere_set R n.+1 ->finite_set E ->
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n*(n-1)%/2)%N (spherical_orthogonal_preimage c E)=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c)*
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n.+1)) 0 E.
Proof.
move=>hc hES hE.
have [F hEF]:=finite_fsetP.1 hE.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R n.+1 n.+1).
pose mu:=@hausdorff_measure R Y (n*(n-1)%/2)%N.
have hMu:is_measure mu:=@hausdorff_measure_is_measure R Y (n*(n-1)%/2)%N.
pose P:=fun a:X=>spherical_orthogonal_preimage c [set a].
have hUnion:spherical_orthogonal_preimage c E=\bigcup_(a in [set` F]) P a.
  apply/seteqP; split=>g.
  - move=>[hg hEg]; exists (g c); first by rewrite -hEF.
    split; first exact hg; reflexivity.
  - move=>[a ha [hg hga]]; split; first exact hg.
    by rewrite hga hEF.
have hMeas a: a \in F ->measure_measurable mu (P a).
  move=>ha.
  have hCompact:=@spherical_orthogonal_preimage_compact R n.+1 c [set a] (@compact_set1 X a).
  exact:(borel_regular_borel_measurable hMu (@hausdorff_measure_borel_regular R Y (n*(n-1)%/2)%N)
    (closed_borel_set (compact_closed (@metric_hausdorff R Y) hCompact))).
have hDisjoint a b: a \in F ->b \in F ->a!=b ->forall g,P a g ->P b g ->False.
  move=>ha hb hne g [_ hga] [_ hgb]; move/eqP:hne; apply.
  exact:(eq_trans (esym hga) hgb).
have hAdd:=@measure_finite_disjoint_additivity R Y X mu hMu P F hMeas hDisjoint.
have hFibre a:a \in F ->mu (P a)=mu (spherical_orthogonal_isotropy c).
  move=>ha; apply:(@spherical_orthogonal_fibre_measure R n c a hc).
  apply:hES; by rewrite hEF.
change (mu (spherical_orthogonal_preimage c E)=mu (spherical_orthogonal_isotropy c)*
  @hausdorff_measure R X 0 E).
rewrite hUnion hAdd hEF hausdorff_zero_counting_measure counting_measure_finite.
have hSum:(\sum_(a<-F) mu (P a))=\sum_(a<-F) mu (spherical_orthogonal_isotropy c).
  rewrite !big_seq; apply:eq_bigr=>a ha; exact:hFibre a ha.
rewrite hSum big_seq_fsetE big_const [RHS]muleC mule_natl /enatmul Monoid.Theory.iteropE.
by rewrite cardfE.
Qed.
