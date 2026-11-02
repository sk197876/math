(** Federer (1969), 3.2.28(2), printed p. 265:
    SO(m) has half the Hausdorff measure of O(m), for
    m positive. An actual orientation-reversing isometric
    involution exchanges the two closed determinant pieces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerProductUP InnerNorm InnerMetric HomInner OrthogonalMaps
  OrthogonalGroupTopology SpecialLinearTopology ExteriorDeterminant AdjointDeterminant
  EuclideanHomInnerCharts EuclideanStiefelInnerSplitting EuclideanExteriorFrameFibres
  EuclideanOrientationReflection InnerMetricLawCompatibility HomeomorphismUP
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffIsometricEmbedding
  MeasureUP MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_special_orthogonal_closed]: the two
    determinant components used in the half-volume assertion,
    Federer 3.2.28(2), p. 265. Closedness follows
    from the proved determinant continuity and orthogonal
    closedness of 2.7.16, pp. 135,139. *)
Lemma euclidean_special_orthogonal_closed (R:realType) m:
  @closed [the topologicalType of inner_metric_space (@euclidean_hom_inner_productP R m m)]
    (@euclidean_special_orthogonal_set R m).
Proof.
pose V:=R_n R m.
pose hB:=@euclidean_inner_productP R m.
pose hb:=@coordinate_basisP R m.
pose hH:=hom_inner_productP hB hB hb.
pose H:=inner_metric_space hH.
have hO:=@orthogonal_maps_closed R V (@euclidean_inner_product R m) hB m
  (@coordinate_basis R m) hb.
have hDet:closed [set u:H|euclidean_det (hom_as_linear u)= 1].
  change (closed ((fun u:H=>(euclidean_det (hom_as_linear u):R^o)) @^-1` [set c|c= 1])).
  apply:preimage_closed; last exact:closed_eq.
  by move=>u _; exact:euclidean_det_continuous.
have hClosed:closed [set u:H|euclidean_special_orthogonal_set u].
  change (closed ((@orthogonal_maps R V (@euclidean_inner_product R m) hB m
    (@coordinate_basis R m) hb) `&` [set u:H|euclidean_det (hom_as_linear u)= 1])).
  exact:closedI hO hDet.
change (closed ((fun u:inner_metric_space (@euclidean_hom_inner_productP R m m)=>(u:H))
  @^-1` [set u:H|euclidean_special_orthogonal_set u])).
apply:preimage_closed; last exact hClosed.
move=>u _; exact:(homeomorphism_continuous
  (inner_metric_law_homeomorphism (@euclidean_hom_inner_productP R m m) hH)).
Qed.

(** Source for [euclidean_special_orthogonal_half_measure]:
    the half-volume assertion in Federer 3.2.28(2),
    p. 265. Equality is proved before any finite-volume
    calculation and holds in every natural Hausdorff degree.
    Positive m is retained because O(0)=SO(0). *)
Local Open Scope ereal_scope.
Theorem euclidean_special_orthogonal_half_measure (R:realType) m:
  (0<m)%N ->forall k,
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m)) k
    [set u|is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R m) (hom_as_linear u)]=
  (2:R)%:E* @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m)) k
    (@euclidean_special_orthogonal_set R m).
Proof.
Local Open Scope ring_scope.
move=>hm k.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R m m).
pose SO:=@euclidean_special_orthogonal_set R m.
pose O:set X:=[set u|is_orthogonal_map (@euclidean_inner_product R m)
  (@euclidean_inner_product R m) (hom_as_linear u)].
pose N:set X:=[set u|O u /\euclidean_det (hom_as_linear u)= -1].
have [r [hr [hrr hdet]]]:=euclidean_orientation_reflection_exists R hm.
pose f:=fun u:X=>(hom_comp r u:X).
have hff:cancel f f by move=>u; apply:hom_ext=>x; exact:hrr.
have hDist u v:mdist (f u) (f v)=mdist u v.
  rewrite !inner_metric_distanceE.
  have hSub:(hom_comp r u-hom_comp r v)=hom_comp r (u-v).
    apply:hom_ext=>x; change (r (u x)-r (v x)=r (u x-v x)).
    by rewrite linearB.
  change (inner_norm (@euclidean_hom_inner_productP R m m) (hom_comp r u-hom_comp r v)=
    inner_norm (@euclidean_hom_inner_productP R m m) (u-v)).
  rewrite hSub; exact:(@euclidean_stiefel_vertical_norm_isometry R m m r hr (u-v)).
have hfO u:O u ->O (f u).
  move=>hu x y; change (euclidean_inner_product (r (u x)) (r (u y))=euclidean_inner_product x y).
  rewrite hr; exact:hu.
have hfDet u:euclidean_det (hom_as_linear (f u))= -euclidean_det (hom_as_linear u).
  have he:hom_as_linear (f u) =1 linear_comp (hom_as_linear r) (hom_as_linear u) by move=>x.
  rewrite /euclidean_det (@det_ext R (euclidean_two_nonzero R) m (R_n R m) (@coordinate_basis R m)
    (@coordinate_basisP R m) (hom_as_linear (f u))
    (linear_comp (hom_as_linear r) (hom_as_linear u)) he) det_comp hdet.
  by rewrite mulN1r.
have hImage:f @` SO=N.
  apply/seteqP; split=>u.
  - move=>[v [hvO hvD] <-]; split; first exact:hfO hvO.
    change (euclidean_det (hom_as_linear v)= 1) in hvD.
    by rewrite hfDet hvD.
  - move=>[huO huD]; exists (f u); last exact:hff.
    split; first exact:hfO huO.
    by change (euclidean_det (hom_as_linear (f u))= 1); rewrite hfDet huD opprK.
have hSplit:O=SO `|` N.
  apply/seteqP; split=>u.
  - move=>hu.
    have hs:=@orthogonal_determinant_square R (euclidean_two_nonzero R)
      (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m)
      m (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear u) hu.
    have hd:(euclidean_det (hom_as_linear u)==1) || (euclidean_det (hom_as_linear u)== -1).
      by rewrite -eqf_sqr expr1n; apply/eqP; exact hs.
    case/orP:hd=>/eqP hd; [left|right]; by split.
  - by move=>[[hu _]|[hu _]].
have hDisjoint u:SO u ->N u ->False.
  move=>[_ hP] [_ hN].
  have he:(1:R)= -1:=eq_trans (esym hP) hN.
  have h1:(0:R)<1:=ltr01; lra.
have hMeas:measure_measurable (@hausdorff_measure R X k) SO.
  apply:(borel_regular_borel_measurable (@hausdorff_measure_is_measure R X k)
    (@hausdorff_measure_borel_regular R X k)).
  exact:(@closed_borel_set [the topologicalType of X] SO
    (@euclidean_special_orthogonal_closed R m)).
have hEqual:=@hausdorff_isometric_embedding_invariance R X X f f hff hDist k SO.
rewrite hImage in hEqual.
change (@hausdorff_measure R X k O=
  ((2:R)%:E* @hausdorff_measure R X k SO)%E).
rewrite hSplit (measure_disjoint_union hMeas hDisjoint) hEqual.
have hTwo:(2:R)= 1+1 by ring.
by rewrite hTwo EFinD (ge0_muleDl _ lee01 lee01) !mul1e.
Qed.
