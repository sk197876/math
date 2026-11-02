(** Federer (1969), 3.1.21, p. 234: exact tangent
    membership in an ambient straightening chart. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormClassOneUP
  NormDifferentialInverseIdentities NormRegularity NormDiffeomorphismUP EuclideanSubmanifoldUP
  TangentConeUP TangentConeLocal TangentClosedSubspace NormDiffeomorphismTangent FiniteNormSubspaceClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_straightening_tangent]: supporting
    the tangent-space and tangent-bundle assertions of Federer
    3.1.21, p. 234. In a straightening chart sigma,
    v belongs to Tan(B,x) exactly when Dsigma(x)v lies
    in the straightened plane, at every x in B intersect T. *)
Theorem submanifold_straightening_tangent (R:realType) n mu k
    (B T C:set (R_n R n)) b (s t:R_n R n->R_n R n) (Z:G (R_n R n) mu)
    (D:R_n R n->Hom (R_n R n) (R_n R n)) :
  (1<=k)%N -> @is_submanifold_straightening R n mu k B b T C s t Z ->
  (forall x,T x -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) T s x (D x)) ->
  forall x,T x -> B x -> forall v,
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B x v <-> grassmann_val Z (D x v).
Proof.
move=>hk hChart hDs x hx hBx v.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hSt:=submanifold_straightening_diffeomorphism hChart.
have him:=submanifold_straightening_image hChart.
have hsx:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hSt x hx.
have htan:=@norm_diffeomorphism_tangent_image R X X NX NX hNX hNX T B C s t k x (D x)
  hk hSt hx (hDs x hx).
rewrite him in htan.
have hCint:norm_domain_interior NX C (s x).
  exact ((@norm_class_continuous R X X NX NX hNX hNX C t k
    (norm_diffeomorphism_inverse_class hSt) (s x) hsx).1).
have hzClosed:=@finite_norm_subspace_closed R X NX hNX n (@coordinate_basis R n)
  (@coordinate_basisP R n) (grassmann_val Z) mu (grassmann_proof Z).
have hsxZ:grassmann_val Z (s x).
  have hh:(s @` (B `&` T)) (s x) by exists x; split.
  rewrite him in hh; exact hh.1.
change (D x @` norm_tangent_cone NX B x=norm_tangent_cone NX ((grassmann_val Z:set X) `&` C) (s x)) in htan.
rewrite (norm_tangent_open_restriction (grassmann_val Z) hCint)
  (@norm_tangent_closed_subspace R X NX hNX (grassmann_val Z) (s x) hzClosed hsxZ) in htan.
have [E hE]:=(@norm_class_firstP R X X NX NX hNX hNX C t).1
  (norm_class_lower hk (norm_diffeomorphism_inverse_class hSt)).
have hmap y (hy:T y):C (s y):=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hSt y hy.
have hts y (hy:T y):t (s y)=y:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k hSt y hy.
have hleft:=@norm_differentials_left_inverse R X X NX NX hNX hNX T C s t x (D x) (E (s x))
  hmap hts (hDs x hx) (norm_class_one_differential hE hsx).
have hcan:cancel (D x) (E (s x)).
  move=>w; exact (congr1 (fun H:Hom X X=>H w) hleft).
have hi:injective (D x):=can_inj hcan.
split.
- move=>hv; rewrite -htan; by exists v.
- move=>hv.
  have hh:(D x @` norm_tangent_cone NX B x) (D x v) by rewrite htan.
  have [u hu heq]:=hh.
  have heuv:u=v:=hi _ _ heq.
  by rewrite -heuv.
Qed.
