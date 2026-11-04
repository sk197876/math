(** Federer (1969), 3.2.47, p. 282: supporting smooth
    assembly of a linear map from its values on the chosen
    orthonormal basis. This is the actual Hom map with its
    Hilbert metric, rather than a replacement coordinate norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP RealNormUP InnerNorm HilbertFormCompactness OrthonormalFamilies
  EuclideanHomInnerCharts EuclideanRankOneInner NormDifferentialUP NormFiniteLinearBound
  NormRegularity NormRegularityOperations NormRegularityLinearMaps NormRegularityFiniteSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_frame_column_map]: supporting linearity
    of the map v to the rank-one operator x to (x.e_i)v,
    used to assemble F in 3.2.47, p. 282. *)
Definition euclidean_frame_column_map (R:realType) m n (w:R_n R m):
    Hom (R_n R n) (Hom (R_n R m) (R_n R n)).
Proof.
apply:(@HomMap R (R_n R n) (Hom (R_n R m) (R_n R n))
  (fun v=>euclidean_rank_one_hom w v)).
apply/asboolP=>c v z; apply:hom_ext=>x.
change (euclidean_inner_product x w*:(c*:v+z)=
  c*:(euclidean_inner_product x w*:v)+euclidean_inner_product x w*:z).
by rewrite scalerDr !scalerA mulrC.
Defined.

(** Source for [euclidean_frame_assembly]: supporting specification
    by the values on an orthonormal basis in 3.2.47,
    p. 282. The finite rank-one sum is an algebraic
    expression in the already public Hom vector space. *)
Definition euclidean_frame_assembly (R:realType) m n
    (e:'I_m->R_n R m) (v:'I_m->R_n R n):=
  \sum_i (@euclidean_frame_column_map R m n (e i)) (v i).

(** Source for [euclidean_frame_assemblyE]: the actual assembled
    linear map has the prescribed values on the orthonormal
    source family, supporting F(e_i)=f_i in 3.2.47, p. 282. *)
Lemma euclidean_frame_assemblyE (R:realType) m n
    (e:'I_m->R_n R m) (v:'I_m->R_n R n):
  orthonormal_family (@euclidean_inner_product R m) e ->
  forall j,euclidean_frame_assembly e v (e j)=v j.
Proof.
move=>he j.
have hEvaluation:euclidean_frame_assembly e v (e j)=
    \sum_i euclidean_inner_product (e j) (e i)*:v i.
  rewrite /euclidean_frame_assembly.
  elim/big_rec2: _=>[|i z w _ hzw]; first by rewrite hom_zeroE.
  by rewrite hom_addE hzw.
rewrite hEvaluation (bigD1 j) // he eqxx scale1r.
have hRest:(\sum_(i | i!=j) euclidean_inner_product (e j) (e i)*:v i)=0.
  apply:big1=>i hij; rewrite he eq_sym (negbTE hij); exact:scale0r.
rewrite hRest; change (v j+0=v j); exact:addr0.
Qed.

(** Source for [euclidean_frame_assembly_norm_class]: smooth
    components give a smooth actual Hom map, supporting the
    regularity of F in 3.2.47, p. 282. Every bound
    is derived from finite dimension and the public norm laws. *)
Theorem euclidean_frame_assembly_norm_class (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) m n (e:'I_m->R_n R m)
    (A:X->Prop) (v:'I_m->X->R_n R n) k:
  (forall x,A x->norm_domain_interior NX A x) ->
  (forall i,norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R n)) A (v i) k) ->
  norm_class hNX (inner_norm_real_norm (@euclidean_hom_inner_productP R m n)) A
    (fun x=>euclidean_frame_assembly e (fun i=>v i x)) k.
Proof.
move=>hOpen hv; apply:(norm_class_finite_sum hOpen)=>i.
apply:(@norm_class_postcompose_linear R X (R_n R n) (Hom (R_n R m) (R_n R n))
  NX (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_hom_inner_productP R m n)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n)) A (v i)
  (@euclidean_frame_column_map R m n (e i)) k _ (hv i)).
exact (@norm_finite_linear_bounded R (R_n R n) (Hom (R_n R m) (R_n R n))
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_hom_inner_productP R m n))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m n))
  n (@coordinate_basis R n) (@coordinate_basisP R n) ((@euclidean_frame_column_map R m n (e i)))).
Qed.
