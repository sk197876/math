(** Federer (1969), 3.1.18, p. 230: the section psi(u)=F(u,w0)
    has the same class as F, and its differential at the centre is
    DF composed with the first-coordinate inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialChain
  NormDifferentialLocal NormClassOneUP NormRegularity NormRegularityOperations
  NormFiniteLinearBound NormOpenDomainLaws EuclideanBlockLinearMaps EuclideanProductBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Sections.
Variable R:realType.
Variables v l:nat.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation X:=(R_n R (v+l)).
Local Notation V:=(R_n R v).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (v+l))).
Local Notation NV:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NW:=(inner_norm (@euclidean_inner_productP R l)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (v+l))).
Local Notation hNV:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation p:=(@euclidean_first_block_map R v l).
Local Notation q:=(@euclidean_last_block_map R v l).
Local Notation i:=(@euclidean_first_injection_map R v l).
Local Notation j:=(@euclidean_last_injection_map R v l).

(** Source for [euclidean_box_section_class]: psi has class k,
    as used for the target change h in Federer 3.1.18, p. 230. *)
Theorem euclidean_box_section_class (c:X) e (F:X->Y) k :
  0<e -> norm_class hNX hNY (@euclidean_product_box R v l c e) F k ->
  norm_class hNV hNY (fun u=>NV (u-p c)<e) (fun u=>F (i u+j (q c))) k.
Proof.
move=>he hF.
pose V0:=fun u:V=>NV (u-p c)<e.
have hopen u (hu:V0 u):norm_domain_interior NV V0 u.
  exact (@norm_open_ball_domain_interior R V NV hNV (p c) e u hu).
have hi:=@norm_finite_linear_bounded R V X NV NX hNV hNX v
  (@coordinate_basis R v) (@coordinate_basisP R v) i.
have hic:=@norm_class_linear R V X NV NX hNV hNX V0 i k hopen hi.
have hconst:=@norm_class_constant R V X NV NX hNV hNX V0 (j (q c)) k hopen.
have hphi:=norm_class_add hic hconst.
have hmap u (hu:V0 u):@euclidean_product_box R v l c e (i u+j (q c)).
  apply: (@euclidean_product_box_coordinates R v l c e u (q c)).2; split=>//.
  by rewrite subrr inner_norm0.
exact (@norm_class_compose_on R V X Y NV NX NY hNV hNX hNY V0
  (@euclidean_product_box R v l c e) (fun u=>i u+j (q c)) F k hmap hphi hF).
Qed.

(** Source for [euclidean_box_section_differential_at_center]: the
    chain-rule expression for Dpsi[(p f)(a)] before identifying it
    with p*, supporting the final paragraph of 3.1.18, p. 230. *)
Theorem euclidean_box_section_differential_at_center (c:X) e (F:X->Y) (L:Hom X Y) :
  0<e -> has_norm_differential NX NY (@euclidean_product_box R v l c e) F c L ->
  has_norm_differential NV NY (fun u=>NV (u-p c)<e)
    (fun u=>F (i u+j (q c))) (p c) (hom_comp L i).
Proof.
move=>he hdF.
pose V0:=fun u:V=>NV (u-p c)<e.
have hv:V0 (p c) by rewrite /V0 subrr inner_norm0.
have hopen:=@norm_open_ball_domain_interior R V NV hNV (p c) e (p c) hv.
have hi:=@norm_finite_linear_bounded R V X NV NX hNV hNX v
  (@coordinate_basis R v) (@coordinate_basisP R v) i.
have hdi:=@norm_differential_linear R V X NV NX hNV hNX V0 (p c) i hopen hi.
have hconst:=@norm_differential_constant R V X NV NX hNV hNX V0 (p c) (j (q c)) hopen.
have hphi:=norm_differential_add hNX hdi hconst; rewrite addr0 in hphi.
have heqc:i (p c)+j (q c)=c:=esym (@euclidean_block_linear_decomposition R v l c).
have hdF':has_norm_differential NX NY (@euclidean_product_box R v l c e) F
    (i (p c)+j (q c)) L by rewrite heqc.
have hchain:=norm_differential_chain hNV hNX hNY hphi hdF'.
have hmap u (hu:V0 u):@euclidean_product_box R v l c e (i u+j (q c)).
  apply: (@euclidean_product_box_coordinates R v l c e u (q c)).2; split=>//.
  by rewrite subrr inner_norm0.
exact (@norm_differential_restrict R V Y NV NY
  (fun u=>V0 u /\ @euclidean_product_box R v l c e (i u+j (q c))) V0
  (fun u=>F (i u+j (q c))) (p c) (hom_comp L i)
  (fun u hu=>conj hu (hmap u hu)) hopen hchain).
Qed.
End Sections.
