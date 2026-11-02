(** Federer (1969), 3.2.3, p. 244: the graph
    differential is injective and its Jacobian has an
    epsilon factor at every singular differential of f.
    Use the orthogonal image frame of 1.7.3. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom HomogeneousHom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormalization Bilinear OrthonormalFamilies OrthogonalImageBasis
  EuclideanBlockLinear EuclideanGraphLift EuclideanLinearJacobian EuclideanOrthonormalJacobian
  EuclideanBlockCoordinates EuclideanLinearMaps SingleFactorProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_linear_graph_inner]: the
    orthogonal block decomposition of Dg in Federer
    3.2.3, p. 244. Its inner product is the
    image inner product plus epsilon squared times the
    source inner product. *)
Lemma euclidean_linear_graph_inner (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) e v w:
  @euclidean_inner_product R (n+m) (euclidean_linear_graph_lift L e v)
    (euclidean_linear_graph_lift L e w)=
    @euclidean_inner_product R n (L v) (L w)+e^+2*@euclidean_inner_product R m v w.
Proof.
rewrite !euclidean_linear_graph_liftE !euclidean_graph_lift_join euclidean_block_join_inner /=.
rewrite (bilZl (inner_bilinear (@euclidean_inner_productP R m)))
  (bilZr (inner_bilinear (@euclidean_inner_productP R m))).
change (@euclidean_inner_product R n (L v) (L w)+e*(e*@euclidean_inner_product R m v w)=
  @euclidean_inner_product R n (L v) (L w)+e^+2*@euclidean_inner_product R m v w).
by rewrite mulrA expr2.
Qed.

(** Source for [euclidean_linear_graph_injective]: the
    univalence of Dg displayed in Federer 3.2.3,
    p. 244, from its nonzero scaled identity block. *)
Lemma euclidean_linear_graph_injective (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) e:
  e!=0 -> injective (euclidean_linear_graph_lift L e).
Proof.
move=>he x y hxy.
apply:(@euclidean_graph_lift_injective R m n L e he x y).
by rewrite -!euclidean_linear_graph_liftE.
Qed.

(** Source for [euclidean_singular_graph_jacobian_bound]:
    J_m g<=epsilon (Lip(f)+epsilon)^(m-1), Federer
    3.2.3, p. 244, with the differential bound M
    explicit. In the adapted orthonormal frame a zero
    image has graph length epsilon; all other lengths
    are at most M+epsilon. *)
Theorem euclidean_singular_graph_jacobian_bound (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) e M:
  0<e -> 0<=M ->
  (forall v,inner_norm (@euclidean_inner_productP R n) (L v)<=
    M*inner_norm (@euclidean_inner_productP R m) v) ->
  ~injective L ->
  euclidean_linear_jacobian m (euclidean_linear_graph_lift L e)<=e*(M+e)^+m.-1.
Proof.
move=>he hM hBound hSing.
have [b [hb [ho hImages]]]:=@orthonormal_orthogonal_image_basis R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (hom_as_linear L) m (@coordinate_basis R m) (@coordinate_basisP R m).
have [i0 hi0]:=@noninjective_orthogonal_frame_zero_image R m n L b ho hImages hSing.
pose G:=euclidean_linear_graph_lift L e.
have hGImages i j:i!=j -> @euclidean_inner_product R (n+m) (G (b i)) (G (b j))=0.
  move=>hij; rewrite /G euclidean_linear_graph_inner (hImages i j hij) (ho i j) (negbTE hij).
  by rewrite mulr0 addr0.
have hJ:=@euclidean_jacobian_orthogonal_frame_images R m (n+m)%N G b ho hGImages.
have hLen i:inner_norm (@euclidean_inner_productP R m) (b i)= 1.
  exact (orthonormal_norm1 (@euclidean_inner_productP R m) ho i).
have hZero:inner_norm (@euclidean_inner_productP R (n+m)) (G (b i0))=e.
  rewrite /G euclidean_linear_graph_liftE euclidean_graph_lift_join hi0.
  change (inner_norm (@euclidean_inner_productP R (n+m))
    (@EuclideanBlockLinearMaps.euclidean_last_injection R n m (e*:b i0))=e).
  by rewrite EuclideanBlockNorms.euclidean_last_injection_norm inner_normZ hLen mulr1 ger0_norm // ltW.
have hZeroBound:inner_norm (@euclidean_inner_productP R (n+m)) (G (b i0))<=e by rewrite hZero.
have hEach i:inner_norm (@euclidean_inner_productP R (n+m)) (G (b i))<=M+e.
  have hh:=euclidean_graph_lift_norm_bound L e (b i).
  rewrite hLen (ger0_norm (ltW he)) mulr1 in hh.
  have hhL:=hBound (b i); rewrite hLen mulr1 in hhL.
  apply:le_trans hh _; exact (lerD hhL (lexx e)).
rewrite hJ.
have hMe:0<=M+e:=addr_ge0 hM (ltW he).
have hh:=@single_factor_product_bound R (Finite.clone 'I_m _)
  (fun i=>inner_norm (@euclidean_inner_productP R (n+m)) (G (b i))) i0 e (M+e)
  (ltW he) hMe (fun i=>inner_norm_nonnegative _ _) hZeroBound
  (fun i _=>hEach i).
by rewrite card_ord in hh.
Qed.
