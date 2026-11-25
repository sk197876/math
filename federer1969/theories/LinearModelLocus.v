(** Federer (1969), 3.2.2, p. 242: the sets Z(s,i)
    retain an actual differential and its uniform small-ball
    remainder. Existence of a suitable member at each injective
    differential is proved from the dense source automorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm RealNormUP NormDifferentialUP HomSpaceTopology EuclideanHomOperator
  FiniteLinearInverseField ExtendedRealReciprocalBounds InjectiveLinearLengthModel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_model_locus]: the Borel sets Z(s,i)
    of Federer 3.2.2, p. 242. Positive integers i in
    the book are represented by successors i+1; the remainder
    condition includes the entire closed ball of radius 1/(i+1). *)
Definition linear_model_locus (R:realType) m n
    (f:R_n R m->R_n R n) (s:Hom (R_n R m) (R_n R m)) (lambda e:R) (i:nat):set (R_n R m):=
  [set a|exists D:Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a D /\
    (forall v,(lambda^-1+e)*inner_norm (@euclidean_inner_productP R m) (s v)<=
      inner_norm (@euclidean_inner_productP R n) (D v) /\
      inner_norm (@euclidean_inner_productP R n) (D v)<=
        (lambda-e)*inner_norm (@euclidean_inner_productP R m) (s v)) /\
    (forall h,inner_norm (@euclidean_inner_productP R m) h<=(i.+1%:R:R)^-1 ->
      inner_norm (@euclidean_inner_productP R n) (f (a+h)-f a-D h)<=
        e*inner_norm (@euclidean_inner_productP R m) (s h))].

(** Source for [linear_model_locus_covers_injective]: the final
    paragraph of Federer 3.2.2, p. 242, with the polar
    isometry direction corrected by erratum p. 4. Density supplies
    the source automorphism, and differentiability plus its bounded
    inverse supplies the natural radius. *)
Theorem linear_model_locus_covers_injective (R:realType) m n
    (f:R_n R m->R_n R n) (S:set (Hom (R_n R m) (R_n R m)))
    (lambda e:R) :
  (forall s,S s -> injective s) ->
  (forall g:Hom (R_n R m) (R_n R m),injective g ->
    forall r:R,0<r -> exists s,S s /\ euclidean_operator_norm (s-g)<r) ->
  1<lambda -> 0<e -> lambda^-1+e<1 -> 1<lambda-e ->
  forall a (D:Hom (R_n R m) (R_n R n)),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f a D ->
    injective D -> exists s,S s /\ exists i,linear_model_locus f s lambda e i a.
Proof.
move=>hS hDense hLam he hmargin1 hmargin2 a D hD hInj.
have hLam0:0<lambda:=lt_trans ltr01 hLam.
have hInv0:0<lambda^-1 by rewrite invr_gt0.
have hAlpha:0<lambda^-1+e by nra.
have [s [hs hVec]]:=dense_automorphism_length_model hDense hInj hAlpha hmargin1 hmargin2.
have [t [hst hts]]:=finite_injective_linear_inverse_exists (@coordinate_basisP R m) (hS s hs).
pose p:=euclidean_operator_norm t.
have hp:0<=p:=hom_operator_norm_nonnegative _ _ _ _.
have hp1:0<p+1 by nra.
pose delta:=e/(p+1).
have hdelta:0<delta by rewrite /delta divr_gt0.
have hEq:delta*(p+1)=e by rewrite /delta divfK // gt_eqF.
have hcoeff:delta* p<=e by nra.
have [d [hd hRem]]:=norm_differential_remainder hD hdelta.
have [i hi]:=positive_reciprocal_nat_small hd.
exists s; split; first exact hs.
exists i,D; split; first exact hD.
split; first exact hVec.
move=>h hh.
have hR:=hRem h Logic.I (le_lt_trans hh hi).
have hInv:=hom_operator_norm_bound (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R m) (@coordinate_basisP R m) t (s h).
rewrite hst in hInv.
change (is_true (inner_norm (@euclidean_inner_productP R m) h<=
  p*inner_norm (@euclidean_inner_productP R m) (s h))) in hInv.
apply:le_trans hR _.
have h1:=ler_wpM2l (ltW hdelta) hInv.
have h2:=ler_wpM2r (inner_norm_nonnegative (@euclidean_inner_productP R m) (s h)) hcoeff.
by rewrite mulrA in h1; exact (le_trans h1 h2).
Qed.
