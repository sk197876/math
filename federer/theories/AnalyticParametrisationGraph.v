(** Federer (1969), 3.1.24, p. 240, referring to 3.1.19, p. 231: the orthogonal graph chart
    follows from the constant-rank normal form, after shrinking the
    parameter ball inside an ambient relatively open image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity NormRegularityOperations NormClassZeroTopology
  NormMetric NormBoundedLinearTopology NormOpenPreimage NormOpenDomainLaws NormLinearDomainLaws
  NormFiniteLinearBound NormDiffeomorphismUP NormRankZero LinearRangeProjectionUP
  EuclideanBlockLinearMaps ConstantRankChartUP ConstantRankTheorem ConstantRankSectionImage
  EuclideanSubmanifoldUP SubmanifoldChartsUP ConstantRankAnalytic AnalyticSubmanifoldChartsUP NormAnalyticLocal NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_open_parametrisations_orthogonal_graphs]: 3.1.24, p. 240: the
    normalized orthogonal projection supplied by 3.1.18 gives
    condition (5) of Federer 3.1.19, p. 231. Applied to (4)'s
    parametrisation, this proves the printed implication (4) to (5). *)
Theorem analytic_open_parametrisations_orthogonal_graphs (R:realType) n mu (B:set (R_n R n)) :
  @has_analytic_open_parametrisations R n mu B ->
  @has_analytic_orthogonal_graphs R n mu B.
Proof.
move=>hB b hb.
have [m [Q [f [D [hmm [hf [hD [hinto [hbim [hr hopen]]]]]]]]]]:=hB b hb.
have [l hm]:exists l,m=(mu+l)%N by exists (m-mu)%N; rewrite addnC subnK.
subst m.
have [a ha hab]:=hbim.
pose X:=R_n R n; pose Y:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NY:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hgen:norm_generic_rank (inner_norm (@euclidean_inner_productP R (mu+l))) Q D a mu.
  have hc:=norm_class_continuous (norm_analytic_class_all_orders hf 0%N).
  have [r [hr0 hball]]:=(@hc a ha).1.
  exists r; split=>// h hh; split; first exact: hball.
  exact: hr (hball h hh).
have [U [e [p [j [g [G [psi [hC [hgA [hGA [hpsiA [hhA hHA]]]]]]]]]]]]:=@federer_3_1_18_analytic R mu l n Q f D a hf hD hgen.
pose V:=@constant_rank_parameter_domain R mu l g a e.
have hP:=constant_rank_projection hC.
have him:psi @` V=f @` U:=constant_rank_section_image hC.
have hrel:=hopen U (constant_rank_domain_subset hC)
  (norm_diffeomorphism_source_open (constant_rank_source_chart hC)).
have [N [hN hUN]]:=hrel.
have hbU:(f @` U) b by exists a; [exact: constant_rank_base_member hC|exact hab].
have hbN:N b by rewrite hUN in hbU; exact hbU.2.
have hpref:@euclidean_first_block_map R mu l (g a)=p b.
  by rewrite (constant_rank_source_prefix hC (constant_rank_base_member hC)) hab.
have hpsi:=constant_rank_section_class hC.
have hcan:=constant_rank_section_right_inverse hC.
have hpsib:psi (p b)=b by rewrite -hpref (constant_rank_section_base hC) hab.
have hbV:V (p b).
  rewrite /V /constant_rank_parameter_domain -hpref subrr inner_norm0.
  exact: constant_rank_radius_positive hC.
have hO:=@norm_class_zero_open_preimage R Y X NY NX hNY hNX V N psi
  (norm_class_continuous hpsi) hN.
have [d [hd hball]]:=proj2 (@norm_domain_interior_neighbourhood R Y NY hNY
  [set u|V u /\ N (psi u)] (p b))
  (open_nbhs_nbhs (conj hO (conj hbV (eq_ind b N hbN (psi (p b)) (esym hpsib))))).
pose W:=fun u:Y=>NY (u-p b)<d.
have hWO u (hu:W u):V u /\ N (psi u).
  have hh:=hball (u-p b) hu; by rewrite addrC subrK in hh.
pose T:=fun x:X=>N x /\ W (p x).
have hpbound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY n
  (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear p).
have hopenW u (hu:W u):norm_domain_interior NY W u.
  exact (@norm_open_ball_domain_interior R Y NY hNY (p b) d u hu).
have hbW:W (p b) by rewrite /W subrr /NY inner_norm0.
have hTb:norm_domain_interior NX T b.
  apply: norm_domain_intersection_interior.
  - exact (proj2 (@norm_domain_interior_neighbourhood R X NX hNX N b)
      (open_nbhs_nbhs (conj hN hbN))).
  - exact (@norm_bounded_linear_preimage_interior R X Y NX NY hNX (hom_of_linear p)
      W b hpbound (hopenW (p b) hbW)).
have hpsiB u (hu:V u):B (psi u).
  have hh:(psi @` V) (psi u) by exists u.
  by rewrite him hUN in hh; exact hh.1.
have hpsiT u (hu:W u):T (psi u).
  split; first exact (hWO u hu).2.
  by rewrite hcan //; exact (hWO u hu).1.
have hpT:p @` T=W.
  apply/seteqP; split=>u.
  - move=>[x hx <-]; exact hx.2.
  - move=>hu; exists (psi u); [exact: hpsiT|exact: hcan (hWO u hu).1].
have hinv x (hx:B x /\ T x):psi (p x)=x.
  have hi:(psi @` V) x by rewrite him hUN; exact: conj hx.1 hx.2.1.
  have [u hu hux]:=hi; by rewrite -hux hcan.
have hcW:=@norm_analytic_open_restriction R Y X NY NX hNY hNX V W psi
  (fun u hu=>(hWO u hu).1) hopenW hpsiA.
have hdpsi:=constant_rank_section_differential hC; rewrite hpref in hdpsi.
have hdW:=@norm_differential_restrict R Y X NY NX V W psi (p b) (hom_of_linear j)
  (fun u hu=>(hWO u hu).1) (hopenW (p b) hbW) hdpsi.
exists T,p,j,psi; split=>//.
split; first exact: range_projection_orthogonal hP.
split; first exact: range_projection_adjoint hP.
split.
- move=>x y hx hy hxy.
  by rewrite -(hinv x hx) -(hinv y hy) hxy.
split.
- rewrite hpT; apply/seteqP; split=>u.
  + move=>[x [hBx hTx] <-]; exact hTx.2.
  + move=>hu; exists (psi u); last exact: hcan (hWO u hu).1.
    exact (conj (@hpsiB u (hWO u hu).1) (@hpsiT u hu)).
rewrite hpT; split; first exact (@norm_open_ball_convex R Y NY hNY (p b) d).
split=>//; split.
- move=>u hu; exact (conj (@hpsiB u (hWO u hu).1) (@hpsiT u hu)).
split; first by move=>u hu; exact: hcan (hWO u hu).1.
by split.
Qed.
