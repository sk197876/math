(** Federer (1969), 3.1.21, p. 234: the tangent cone of
    a class-one submanifold is a vector space of its dimension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormDifferentialInverseIdentities NormRegularity NormDiffeomorphismUP EuclideanSubmanifoldUP
  EuclideanDerivativeLiftDiffeomorphism TangentConeUP TangentConeLocal TangentClosedSubspace
  NormDiffeomorphismTangent FiniteNormSubspaceClosed GrassmannInjectiveImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_tangent_plane]: Tan(B,b) is a
    mu-dimensional vector subspace for b in a mu-dimensional
    class-k submanifold with k>=1, Federer 3.1.21, p. 234.
    The plane is obtained from a straightening chart and the
    exact tangent-image theorem, including mu=0 and n=0. *)
Theorem submanifold_tangent_plane (R:realType) n mu k (B:set (R_n R n)) b :
  (1<=k)%N -> @is_euclidean_submanifold R n mu k B -> B b ->
  exists W:G (R_n R n) mu,norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B b=
    (grassmann_val W:set (R_n R n)).
Proof.
case:k=>[|k] hk hB hb; first by [].
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have [T [C [s [t [Z hChart]]]]]:=hB b hb.
have hTb:=submanifold_straightening_neighbourhood hChart.
have hbT:=norm_domain_interior_member hNX hTb.
have hSt:=submanifold_straightening_diffeomorphism hChart.
have him:=submanifold_straightening_image hChart.
have [D [E [hDf [hDg hLift]]]]:=euclidean_derivative_lift_diffeomorphism hSt.
pose L:=D b.
pose M:=E (s b).
have hsb:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k.+1 hSt b hbT.
have hsf x (hx:T x):C (s x):=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k.+1 hSt x hx.
have htg y (hy:C y):T (t y):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX T C s t k.+1 hSt y hy.
have hts x (hx:T x):t (s x)=x:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k.+1 hSt x hx.
have hst y (hy:C y):s (t y)=y:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX T C s t k.+1 hSt y hy.
have hleft:cancel L M.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX T C s t b L M
    hsf hts (hDf b hbT) (hDg _ hsb).
  move=>v; exact (congr1 (fun H:Hom X X=>H v) he).
have hright:cancel M L.
  have hd:has_norm_differential NX NX T s (t (s b)) L.
    rewrite (hts b hbT); exact: hDf b hbT.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX C T t s (s b) M L
    htg hst (hDg _ hsb) hd.
  move=>v; exact (congr1 (fun H:Hom X X=>H v) he).
have htan:=@norm_diffeomorphism_tangent_image R X X NX NX hNX hNX T B C s t k.+1 b L
  hk hSt hbT (hDf b hbT).
change (L @` norm_tangent_cone NX B b=norm_tangent_cone NX (s @` (B `&` T)) (s b)) in htan.
rewrite him in htan.
have hCint:norm_domain_interior NX C (s b).
  exact ((@norm_class_continuous R X X NX NX hNX hNX C t k.+1
    (norm_diffeomorphism_inverse_class hSt) (s b) hsb).1).
have hzClosed:=@finite_norm_subspace_closed R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) (grassmann_val Z) mu (grassmann_proof Z).
have hsbZ:grassmann_val Z (s b).
  have hh:(s @` (B `&` T)) (s b) by exists b; split.
  rewrite him in hh; exact hh.1.
have heq:L @` norm_tangent_cone NX B b=(grassmann_val Z:set X).
  change (L @` norm_tangent_cone NX B b=norm_tangent_cone NX ((grassmann_val Z:set X) `&` C) (s b)) in htan.
  rewrite (norm_tangent_open_restriction (grassmann_val Z) hCint) in htan.
  rewrite (@norm_tangent_closed_subspace R X NX hNX (grassmann_val Z) (s b) hzClosed hsbZ) in htan.
  exact htan.
have [W hW]:=@grassmann_injective_image R X X mu Z M n (@coordinate_basis R n)
  (@coordinate_basisP R n) (can_inj hright).
exists W; rewrite hW; apply/seteqP; split=>v.
- move=>hv.
  have hLv:grassmann_val Z (L v) by rewrite -heq; by exists v.
  exists (L v)=>//; exact: hleft v.
- move=>[z hz hzv].
  have hh:(L @` norm_tangent_cone NX B b) z by rewrite heq.
  have [u hu huz]:=hh.
  have heuv:u=v by rewrite -(hleft u) huz hzv.
  by rewrite -heuv.
Qed.
