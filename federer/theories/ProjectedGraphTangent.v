(** Federer (1969), 3.1.23, pp. 236–237: the
    affine target plane is the tangent plane of the orthogonal graph. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormDifferentialUP NormFiniteLinearBound NormMetric
  TangentConeUP TangentConeLocal SectionTangentImage FiniteNormLinearRangeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [projected_graph_tangent]: identifying Tan(B,b)
    with im p* in Federer 3.1.23, pp. 236–237,
    using the graph chart of 3.1.19(5) and tangent
    transport of 3.1.21. The parametrisation is its actual
    inverse and its differential is the given injection j. *)
Lemma projected_graph_tangent (R:realType) n mu (B T:set (R_n R n))
    (p:{linear R_n R n->R_n R mu}) (j:{linear R_n R mu->R_n R n})
    (psi:R_n R mu->R_n R n) b :
  B b -> norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) T b ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R n)) (p @` T) psi (p b) (hom_of_linear j) ->
  (forall u,(p @` T) u -> B (psi u) /\ T (psi u)) ->
  (forall u,(p @` T) u -> p (psi u)=u) ->
  (forall x,B x -> T x -> psi (p x)=x) ->
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B b=
    range (hom_of_linear j).
Proof.
move=>hb hTb hD hrange hcan hinv.
pose X:=R_n R n; pose Z:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R mu).
have hpb:norm_bounded_linear NX NZ (hom_of_linear p).
  exact (@norm_finite_linear_bounded R X Z NX NZ hNX hNZ n
    (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear p)).
have him:psi @` (p @` T)=B `&` T.
  apply/seteqP; split=>x.
  - move=>[u hu <-]; exact (hrange u hu).
  - move=>[hx ht]; exists (p x); first by exists x.
    exact (hinv x hx ht).
have hclosed:=@finite_norm_linear_range_closed R Z X NX hNX n
  (@coordinate_basis R n) (@coordinate_basisP R n) (hom_of_linear j).
have he:=@norm_section_tangent_image R Z X NZ NX hNZ hNX (p @` T) psi (p b)
  (hom_of_linear j) (hom_of_linear p) hD hpb hcan hclosed.
have hbT:=norm_domain_interior_member hNX hTb.
rewrite (hinv b hb hbT) him (@norm_tangent_open_restriction R X NX B T b hTb) in he.
exact he.
Qed.
