(** Federer (1969), 3.1.21, p. 234: normal vectors
    in straightening charts are carried by the inverse derivative
    adjoint to the perpendicular complement of the fixed plane. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerProductUP NormDifferentialUP
  NormDifferentialInverseIdentities NormDiffeomorphismUP EuclideanSubmanifoldUP TangentConeUP NormalConeUP
  EuclideanAdjoint SubmanifoldStraighteningTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_straightening_normal]: supporting
    the normal-bundle assertion of Federer 3.1.21, p. 234.
    Normal cone inequalities become equalities on the tangent
    vector space, and the inverse derivative adjoint identifies
    the normal vectors with the fixed plane's perpendicular complement. *)
Theorem submanifold_straightening_normal (R:realType) n mu k
    (B T C:set (R_n R n)) b (s t:R_n R n->R_n R n) (Z:G (R_n R n) mu)
    (D E:R_n R n->Hom (R_n R n) (R_n R n)) :
  (1<=k)%N -> @is_submanifold_straightening R n mu k B b T C s t Z ->
  (forall x,T x -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) T s x (D x)) ->
  (forall y,C y -> has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) C t y (E y)) ->
  forall x,T x -> B x -> forall u,
    inner_normal_cone (inner_norm (@euclidean_inner_productP R n)) (@euclidean_inner_product R n) B x u <->
    forall w,grassmann_val Z w -> @euclidean_inner_product R n
      (@euclidean_adjoint R n (E (s x)) u) w=0.
Proof.
move=>hk hChart hDs hDt x hx hBx u.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose BP:=@euclidean_inner_product R n.
pose hB:=@euclidean_inner_productP R n.
pose L:=D x.
pose M:=E (s x).
have hSt:=submanifold_straightening_diffeomorphism hChart.
have hsf y (hy:T y):C (s y):=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hSt y hy.
have htg y (hy:C y):T (t y):=@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX T C s t k hSt y hy.
have hts y (hy:T y):t (s y)=y:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k hSt y hy.
have hst y (hy:C y):s (t y)=y:=@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX T C s t k hSt y hy.
have hsx:=hsf x hx.
have hleft:cancel L M.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX T C s t x L M
    hsf hts (hDs x hx) (hDt _ hsx).
  move=>v; exact (congr1 (fun H:Hom X X=>H v) he).
have hright:cancel M L.
  have hd:has_norm_differential NX NX T s (t (s x)) L.
    rewrite (hts x hx); exact: hDs x hx.
  have he:=@norm_differentials_left_inverse R X X NX NX hNX hNX C T t s (s x) M L
    htg hst (hDt _ hsx) hd.
  move=>v; exact (congr1 (fun H:Hom X X=>H v) he).
have htan v:norm_tangent_cone NX B x v <-> grassmann_val Z (L v).
  exact (@submanifold_straightening_tangent R n mu k B T C b s t Z D
    hk hChart hDs x hx hBx v).
have hpair v:BP (@euclidean_adjoint R n M u) v=BP u (M v).
  exact (eq_trans (@inner_symmetric R X BP hB (@euclidean_adjoint R n M u) v)
    (eq_trans (@euclidean_adjoint_pairing R n M v u) (@inner_symmetric R X BP hB (M v) u))).
change (inner_normal_cone NX BP B x u <-> forall w,grassmann_val Z w ->
  BP (@euclidean_adjoint R n M u) w=0).
split.
- move=>hNor w hw.
  have hv:norm_tangent_cone NX B x (M w).
    apply: (htan _).2; by rewrite hright.
  have hvN:norm_tangent_cone NX B x (-(M w)).
    apply: (htan _).2; rewrite linearN /= hright.
    exact: subspace_opp hw.
  have hplus:BP u (M w)<=0:=hNor _ hv.
  have hminus:BP u (-(M w))<=0:=hNor _ hvN.
  have hsum:BP u (M w)+BP u (-(M w))=0.
    by rewrite /BP -(bilDr (inner_bilinear hB)) addrN (bil0r (inner_bilinear hB)).
  rewrite hpair; lra.
- move=>horth v hv.
  have hz:grassmann_val Z (L v):=(htan v).1 hv.
  have hh:=horth _ hz; rewrite hpair hleft in hh.
  by rewrite hh.
Qed.
