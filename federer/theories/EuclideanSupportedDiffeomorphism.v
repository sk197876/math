(** Federer (1969), 3.1.23, p. 237: a supported
    small perturbation of identity is a global diffeomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom TensorUP RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric FiniteNormMetricPolish
  FiniteNormEquivalence NormDifferentialUP NormDifferentialLinear NormDifferentialSubtraction
  NormClassOneUP NormClassZeroTopology NormClassOneInverse NormRegularity NormRegularityOperations
  NormDiffeomorphismUP NormDifferentialConvexBound NearIdentityNormBall SmallIdentityPerturbation
  SupportedMapProper ProperContinuousClosed NormSpaceConnected EuclideanSmallLinearInverse
  NormInvertibleDifferentialOpen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_supported_small_diffeomorphism]: the
    concluding argument of Federer 3.1.23, p. 237.
    The derivative estimate gives global increment bounds and
    injectivity. The inverse-function theorem gives openness;
    compact support gives properness and hence a closed image;
    connectedness gives surjectivity. Both inverse regularity and
    the inverse Lipschitz estimate are proved, including dimension zero. *)
Theorem euclidean_supported_small_diffeomorphism (R:realType) n k
    (f:R_n R n->R_n R n) (D:R_n R n->Hom (R_n R n) (R_n R n)) c
    (K:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) :
  0<=c<1 ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT f k ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) setT f D ->
  (forall a v,inner_norm (@euclidean_inner_productP R n) (D a v-v)<=
    c*inner_norm (@euclidean_inner_productP R n) v) ->
  compact K -> (forall x,~K x -> f x=x) ->
  exists g,is_norm_diffeomorphism
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT setT f g k /\
    (forall x y,inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
      (1+c)*inner_norm (@euclidean_inner_productP R n) (x-y)) /\
    forall x y,inner_norm (@euclidean_inner_productP R n) (g x-g y)<=
      (1-c)^-1*inner_norm (@euclidean_inner_productP R n) (x-y).
Proof.
move=>hc hf hF hsmall hK hfix.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose M:=real_norm_metric_space hN.
have hcomplete:=@finite_norm_metric_complete R X N hN n
  (@coordinate_basis R n) (@coordinate_basisP R n).
pose Id:=hom_of_linear (linear_id X).
have hId:norm_bounded_linear N N Id.
  exists 1; split; first exact: ler01.
  by move=>v; rewrite /Id hom_of_linearE /= mul1r.
have hder a (_:True):exists L:Hom X X,
    has_norm_differential N N setT (fun x=>f x-x) a L /\
    forall v,N (L v)<=c*N v.
  have hfa:=@norm_class_one_differential R X X N N setT f D hF a Logic.I.
  have hid:=@norm_differential_linear R X X N N hN hN setT a Id
    (norm_differential_interior hfa) hId.
  exists (D a-Id); split.
  - exact (norm_differential_subtract hN hN hfa hid).
  - move=>v; exact (hsmall a v).
have hconv:=@norm_differential_convex_bound R X X N N hN hN setT setT
  (fun x=>f x-x) c (fun _ _ _ _ _ _ _=>Logic.I) (andP hc).1 hder.
have herr x y:N ((f x-x)-(f y-y))<=c*N (x-y).
  exact (hconv x y Logic.I Logic.I).
have hbounds:=norm_identity_perturbation_bounds hN herr.
have hinj:injective f.
  move=>x y hxy; exact (@near_identity_norm_injective R X N hN f setT c (andP hc).2
    (fun x y _ _=>herr x y) x y Logic.I Logic.I hxy).
have hInv a (_:True):exists E:Hom X X,norm_bounded_linear N N E /\
    cancel (D a) E /\ cancel E (D a).
  exact (euclidean_small_linear_inverse (andP hc).2 (hsmall a)).
have ho:@open M (f @` setT).
  exact (@norm_invertible_differential_image_open R X X N N hN hN hcomplete setT f D hF hInv).
have hcont:continuous (fun x:M=>(f x:M)).
  move=>a; exact (@norm_class_zero_continuous_at R X X N N hN hN setT f a
    (norm_class_one_zero hF) Logic.I).
have hproper:=compact_identity_support_proper (@metric_hausdorff R M) hK hcont hfix.
have hclosed:@closed M (f @` setT).
  exact (proper_continuous_map_closed (@metric_hausdorff R M)
    (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN)
    hcont hproper closedT).
have hnon:(f @` setT)!=set0 by exists (f 0); exists 0.
have hrelO:exists2 C:set M,@open M C & (f @` setT)=setT `&` C.
  exists (f @` setT); first exact ho; by rewrite setTI.
have hrelC:exists2 C:set M,@closed M C & (f @` setT)=setT `&` C.
  exists (f @` setT); first exact hclosed; by rewrite setTI.
have hwhole:(f @` setT)=setT:=
  @real_norm_space_connected R X N hN (f @` setT) hnon hrelO hrelC.
have hsurj y:exists x,f x=y.
  have hy:(f @` setT) y by rewrite hwhole.
  by have [x _ hxy]:=hy; exists x.
have [g hfg]:=choice hsurj.
have hgf x:g (f x)=x:=hinj _ _ (hfg (f x)).
have hex x:=hInv x Logic.I.
have [E hE]:=choice hex.
have hgi:=@norm_class_one_inverse R X X N N hN hN hcomplete setT setT f g D E
  hF (fun x _=>(hE x).1) (fun x _=>(hE x).2.1) (fun x _=>(hE x).2.2)
  (fun x _=>conj Logic.I (hgf x)) (fun y _=>conj Logic.I (hfg y)).
have hg1: norm_class hN hN setT g 1%N:=(norm_class_firstP hN hN setT g).2 hgi.
have hgk:=norm_class_inverse_from_first (fun _ _=>Logic.I) (fun _ _=>Logic.I)
  (fun x _=>hgf x) (fun y _=>hfg y) hf hg1.
exists g; split.
- constructor=>//.
  exists Id,Id; split=>//; split=>//; by split.
split; first by move=>x y; exact (hbounds x y).2.
move=>x y.
have hb: (1-c)*N (g x-g y)<=N (x-y).
  have hh:=(hbounds (g x) (g y)).1; by rewrite !hfg in hh.
have hp:0<1-c by have :=(andP hc).2; lra.
change (is_true (N (g x-g y)<=(1-c)^-1*N (x-y))).
rewrite mulrC ler_pdivlMr // mulrC; exact hb.
Qed.
