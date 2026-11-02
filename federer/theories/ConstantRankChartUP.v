(** Federer (1969), 3.1.18, pp. 229–230: construction of the local
    source chart and preservation of both ranks before the fibre step.
    Source dimension is written v+l, covering every v<=m, including l=0.
    Complementary coordinates use the existing sealed linear chart;
    the target projection remains the printed orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormRegularity
  NormDiffeomorphismUP LinearRangeProjectionUP NormSectionShearUP
  EuclideanBlockLinearMaps EuclideanProductBox.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ConstantRankSpecification.
Variable R:realType.
Variables v l n:nat.
Local Notation X:=(R_n R (v+l)).
Local Notation Y:=(R_n R n).
Local Notation V:=(R_n R v).
Local Notation BX:=(@euclidean_inner_product R (v+l)).
Local Notation BY:=(@euclidean_inner_product R n).
Local Notation BV:=(@euclidean_inner_product R v).
Local Notation hBX:=(@euclidean_inner_productP R (v+l)).
Local Notation hBY:=(@euclidean_inner_productP R n).
Local Notation hBV:=(@euclidean_inner_productP R v).
Local Notation NX:=(inner_norm hBX).
Local Notation NY:=(inner_norm hBY).
Local Notation NV:=(inner_norm hBV).
Local Notation hNX:=(inner_norm_real_norm hBX).
Local Notation hNY:=(inner_norm_real_norm hBY).
Local Notation hNV:=(inner_norm_real_norm hBV).
Local Notation Ib:=(@euclidean_first_injection_map R v l).
Local Notation Jb:=(@euclidean_last_injection_map R v l).
Local Notation rb:=(@euclidean_first_block_map R v l).
Local Notation qb:=(@euclidean_last_block_map R v l).



(** Source for [constant_rank_parameter_domain]: the convex parameter
    neighbourhood V in Federer 3.1.18, pp. 229–230, specified as its
    actual coordinate ball. *)
Definition constant_rank_parameter_domain (g:X->X) a e : set V :=
  fun u=>NV (u-rb (g a))<e.

(** Source for [constant_rank_target_domain]: p inverse(V), the actual
    domain and image of the target diffeomorphism in 3.1.18, p. 230. *)
Definition constant_rank_target_domain (g:X->X) a e (p:{linear Y->V}) : set Y :=
  fun y=>constant_rank_parameter_domain g a e (p y).

(** Source for [is_euclidean_constant_rank_chart]: abstract specification
    of the local constant-rank normal form, Federer 3.1.18, pp. 229–230.
    The existence theorem proves these laws; the record introduces no
    project axiom or assumed existence. Product coordinates are encoded
    by the standard linear identification with R^(v+l). *)
Record is_euclidean_constant_rank_chart k (A:set X) (f:X->Y) (D:X->Hom X Y)
    a (U:set X) e (p:{linear Y->V}) (j:{linear V->Y}) (g G:X->X) (psi:V->Y) : Prop := {
  (** Source for [constant_rank_radius_positive]: the parameter balls
      are neighbourhoods, supporting 3.1.18, p. 229. *)
  constant_rank_radius_positive : 0<e;
  (** Source for [constant_rank_base_member]: U is a neighbourhood of
      the generic point a, Federer 3.1.18, p. 229. *)
  constant_rank_base_member : U a;
  (** Source for [constant_rank_domain_subset]: U lies in the actual
      domain of f, supporting 3.1.18, p. 229. *)
  constant_rank_domain_subset : forall x, U x -> A x;
  (** Source for [constant_rank_projection]: p belongs to O*(n,v) and
      image p*=image Df(a), Federer 3.1.18, p. 229. *)
  constant_rank_projection : is_linear_range_projection BY (D a) p j;
  (** Source for [constant_rank_source_chart]: g restricted to U is a
      class-k diffeomorphism onto V times W, 3.1.18, p. 229. *)
  constant_rank_source_chart : is_norm_diffeomorphism hNX hNX U
    (@euclidean_product_box R v l (g a) e) g G k;
  (** Source for [constant_rank_source_prefix]: p f=r g on U,
      Federer 3.1.18, p. 230. *)
  constant_rank_source_prefix : forall x, U x -> rb (g x)=p (f x);
  (** Source for [constant_rank_section_class]: the section psi is of
      class k, as used in Federer 3.1.18, p. 230. *)
  constant_rank_section_class : norm_class hNV hNY (constant_rank_parameter_domain g a e) psi k;
  (** Source for [constant_rank_section_right_inverse]: p psi=id_V,
      Federer 3.1.18, p. 230, displayed section identity. *)
  constant_rank_section_right_inverse : forall u,
    constant_rank_parameter_domain g a e u -> p (psi u)=u;
  (** Source for [constant_rank_section_factor]: f restricted to U=
      psi p f restricted to U, Federer 3.1.18, p. 230. *)
  constant_rank_section_factor : forall x, U x -> f x=psi (p (f x));
  (** Source for [constant_rank_section_formula]: psi(u)=F(u,w0),
      where F=f composed with g inverse, Federer 3.1.18, p. 230. *)
  constant_rank_section_formula : forall u, constant_rank_parameter_domain g a e u ->
    psi u=f (G (Ib u+Jb (qb (g a))));
  (** Source for [constant_rank_section_base]: psi[(p f)(a)]=f(a),
      supporting the derivative normalization in 3.1.18, p. 230. *)
  constant_rank_section_base : psi (rb (g a))=f a;
  (** Source for [constant_rank_section_differential]: Dpsi[(p f)(a)]=p*,
      the penultimate differential identity in 3.1.18, p. 230. *)
  constant_rank_section_differential : has_norm_differential NV NY
    (constant_rank_parameter_domain g a e) psi (rb (g a)) (hom_of_linear j);
  (** Source for [constant_rank_target_chart]: h=identity+p*p-psi p
      is a class-k diffeomorphism of p inverse(V), with inverse
      identity-p*p+psi p, Federer 3.1.18, p. 230. *)
  constant_rank_target_chart : is_norm_diffeomorphism hNY hNY
    (constant_rank_target_domain g a e p) (constant_rank_target_domain g a e p)
    (@norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi)
    (@norm_section_shear_inverse R Y V (hom_of_linear p) (hom_of_linear j) psi) k;
  (** Source for [constant_rank_normal_form]: h f restricted to U=
      p* r g restricted to U, Federer 3.1.18, p. 230. *)
  constant_rank_normal_form : forall x, U x ->
    @norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi (f x)=j (rb (g x));
  (** Source for [constant_rank_image]: h[f(U)]=p*(V), contained in
      image Df(a), Federer 3.1.18, p. 230. The containment follows
      from the prescribed projection-image law. *)
  constant_rank_image :
    (@norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi) @` (f @` U)=
    j @` (constant_rank_parameter_domain g a e);
  (** Source for [constant_rank_factorisation]: f restricted to U=
      h inverse p* r g restricted to U, Federer 3.1.18, p. 230. *)
  constant_rank_factorisation : forall x, U x -> f x=
    @norm_section_shear_inverse R Y V (hom_of_linear p) (hom_of_linear j) psi (j (rb (g x)));
  (** Source for [constant_rank_target_differential]: Dh[f(a)]=identity,
      the final display of Federer 3.1.18, p. 230. *)
  constant_rank_target_differential : has_norm_differential NY NY
    (constant_rank_target_domain g a e p)
    (@norm_section_shear R Y V (hom_of_linear p) (hom_of_linear j) psi)
    (f a) (hom_of_linear (linear_id Y))
}.
End ConstantRankSpecification.
