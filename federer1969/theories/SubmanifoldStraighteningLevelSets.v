(** Federer (1969), 3.1.19, p. 231: condition (1) implies (2).
    The complementary coordinates of a straightening have full
    target rank; their zero set is precisely the local submanifold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP
  NormDifferentialInverseIdentities NormClassOneUP NormRegularity NormRegularityOperations
  NormClassOneLinearPostcompose NormFiniteLinearBound NormOpenDomainLaws NormDiffeomorphismUP
  LinearRankUP LinearRankAtLeast LinearSurjectiveRank EuclideanBlockLinearMaps
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldBasicLaws SubmanifoldBlockStraightening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [submanifold_regular_level_charts]: implication
    (1) to (2), Federer 3.1.19, p. 231. The target dimension is
    n-mu, not an additional larger ambient target. Surjectivity of
    the differential follows from differentiating the actual inverse. *)
Theorem submanifold_regular_level_charts (R:realType) n mu k (B:set (R_n R n)) :
  (1<=k)%N -> @is_euclidean_submanifold R n mu k B ->
  @has_regular_level_charts R n mu k B.
Proof.
move=>hk hB b hb.
have hmn:=submanifold_dimension_at_point hB hb.
have [l hn]:exists l,n=(mu+l)%N by exists (n-mu)%N; rewrite subnKC.
subst n.
have [T [C [s [t [hTb [hD hplane]]]]]]:=submanifold_standard_block_chart hB hb.
pose X:=R_n R (mu+l); pose Y:=R_n R l.
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose NY:=inner_norm (@euclidean_inner_productP R l).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R l).
pose q:=@euclidean_last_block_map R mu l.
pose j:=@euclidean_last_injection_map R mu l.
have hs:=norm_diffeomorphism_forward_class hD.
have ht:=norm_diffeomorphism_inverse_class hD.
have [D hDs]:=(norm_class_firstP hNX hNX T s).1 (norm_class_lower hk hs).
have [E hEt]:=(norm_class_firstP hNX hNX C t).1 (norm_class_lower hk ht).
have hq:=@norm_finite_linear_bounded R X Y NX NY hNX hNY (mu+l)
  (@coordinate_basis R (mu+l)) (@coordinate_basisP R (mu+l)) q.
have hopenT x (hx:T x):norm_domain_interior NX T x.
  have hh:=norm_class_continuous hs; exact (@hh x hx).1.
have hqc:=@norm_class_linear R X Y NX NY hNX hNY (fun _=>True) q k
  (fun x _=>norm_full_domain_interior NX x) hq.
have hf:=@norm_class_compose_on R X X Y NX NX NY hNX hNX hNY T (fun _=>True) s q k
  (fun _ _=>I) hs hqc.
have hDf:=@norm_class_one_linear_postcompose R X X Y NX NX NY hNX hNY T s D q hDs hq.
have hr x (hx:T x):has_linear_rank (hom_comp q (D x)) l.
  have hsxC:=@norm_diffeomorphism_maps R X X NX NX hNX hNX T C s t k hD x hx.
  have hdx:=@norm_class_one_differential R X X NX NX T s D hDs x hx.
  have hdt:=@norm_class_one_differential R X X NX NX C t E hEt (s x) hsxC.
  have htx:=@norm_diffeomorphism_left_inverse R X X NX NX hNX hNX T C s t k hD x hx.
  have hdx':has_norm_differential NX NX T s (t (s x)) (D x) by rewrite htx.
  have hright:=@norm_differentials_left_inverse R X X NX NX hNX hNX C T t s (s x)
    (E (s x)) (D x)
    (@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX T C s t k hD)
    (@norm_diffeomorphism_right_inverse R X X NX NX hNX hNX T C s t k hD) hdt hdx'.
  apply: (@linear_rank_from_full_threshold R X Y l (@coordinate_basis R l)
    (@coordinate_basisP R l) (hom_comp q (D x))).
  apply: (@linear_surjective_rank_at_least R X Y l (@coordinate_basis R l)
    (@coordinate_basisP R l) (hom_comp q (D x)))=>u.
  exists (E (s x) (j u)).
  have hi:=congr1 (fun L:Hom X X=>L (j u)) hright.
  rewrite hom_compE hom_of_linearE /= in hi.
  rewrite hom_compE hi; exact (@euclidean_last_block_injectionK R mu l u).
have hbT:T b:=norm_domain_interior_member hNX hTb.
have hqb:q (s b)=0:=(hplane b hbT).1 hb.
exists l,T,(fun x=>q (s x)),(fun x=>hom_comp q (D x)).
split=>//; split=>//; rewrite addKn.
split; first exact: leqnn.
split=>//; split=>//; split; last exact hr.
apply/seteqP; split=>x.
- move=>[hBx hTx]; split=>//; by rewrite (hplane x hTx).1 // hqb.
- move=>[hTx heq]; split=>//; apply: (hplane x hTx).2.
  by rewrite heq hqb.
Qed.
