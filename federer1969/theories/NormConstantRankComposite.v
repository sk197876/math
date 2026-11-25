(** Federer (1969), 3.1.18, p. 230: the differential of
    F=f composed with g inverse has kernel containing ker r.
    Every differential used below is the actual differential on its
    open domain, and the inverse identities are differentiated. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormClassOneUP NormDifferentialFiniteCalculus NormDifferentialChain
  NormDifferentialLocal NormDifferentialDirectional NormDifferentialInverseIdentities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_constant_rank_composite_differential]: the
    equality of kernels after the source change in Federer 3.1.18,
    p. 230, and its zero derivative on W-directions. This supporting
    form needs only equality of the original kernels, not dimensions;
    the latter is supplied by the preceding finite-rank argument. *)
Theorem norm_constant_rank_composite_differential (R:realType) (X Y V:lmodType R)
    (NX:X->R) (NY:Y->R) (NV:V->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (U C:X->Prop) (f:X->Y) (g G:X->X)
    (Df:X->Hom X Y) (Dg DG:X->Hom X X) (p:Hom Y V) (r:Hom X V) :
  is_norm_class_one_field NX NY U f Df ->
  is_norm_class_one_field NX NX U g Dg ->
  is_norm_class_one_field NX NX C G DG ->
  norm_bounded_linear NY NV p -> norm_bounded_linear NX NV r ->
  (forall x, U x -> C (g x)) -> (forall y, C y -> U (G y)) ->
  (forall y, C y -> g (G y)=y) ->
  (forall x, U x -> r (g x)=p (f x)) ->
  (forall x, U x -> forall z, p (Df x z)=0 -> Df x z=0) ->
  forall y, C y ->
    has_norm_differential NX NY C (fun y=>f (G y)) y (hom_comp (Df (G y)) (DG y)) /\
    forall z, r z=0 -> Df (G y) (DG y z)=0.
Proof.
move=>hf hg hG hp hr hgC hGU hgG hprefix hker y hy.
have hx:=hGU y hy.
have hdf:=norm_class_one_differential hf hx.
have hdg:=norm_class_one_differential hg hx.
have hdG:=norm_class_one_differential hG hy.
split.
- have hcomp:=norm_differential_chain hNX hNX hNY hdG hdf.
  exact (@norm_differential_restrict R X Y NX NY (fun z=>C z /\ U (G z)) C
    (fun z=>f (G z)) y (hom_comp (Df (G y)) (DG y)) (fun z hz=>conj hz (hGU z hz))
    (norm_differential_interior hdG) hcomp).
- have hrd:=@norm_differential_postcompose R X X V NX NX NV hNX U g
    (G y) (Dg (G y)) r hdg hr.
  have hpd:=@norm_differential_postcompose R X Y V NX NY NV hNX U f
    (G y) (Df (G y)) p hdf hp.
  have heq:=norm_differential_unique hNX hNV
    (norm_differential_domain_agreement hNX hprefix hrd) hpd.
  have hInv:=@norm_differentials_left_inverse R X X NX NX hNX hNX C U G g
    y (DG y) (Dg (G y)) hGU hgG hdG hdg.
  move=>z hz.
  have hpoint:=congr1 (fun L:Hom X X=>L z) hInv.
  change (Dg (G y) (DG y z)=z) in hpoint.
  have hproj:=congr1 (fun L:Hom X V=>L (DG y z)) heq.
  change (r (Dg (G y) (DG y z))=p (Df (G y) (DG y z))) in hproj.
  apply (@hker (G y) hx (DG y z)).
  by rewrite -hproj hpoint.
Qed.
