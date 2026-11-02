(** Federer (1969), 3.1.18, p. 230, supporting 3.1.19, p. 231:
    the section psi has exactly the local constant-rank image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormDiffeomorphismUP
  EuclideanBlockLinearMaps EuclideanProductBox ConstantRankChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_rank_section_image]: the section
    psi(u)=F(u,w0) parametrises f(U), from the displayed identities
    in Federer 3.1.18, p. 230; supporting (4) implies (5) of
    3.1.19, p. 231. The image equation is derived, not assumed. *)
Lemma constant_rank_section_image (R:realType) v l n k
    (A U:set (R_n R (v+l))) (f:R_n R (v+l)->R_n R n)
    (D:R_n R (v+l)->Hom (R_n R (v+l)) (R_n R n)) a e p j g G psi :
  @is_euclidean_constant_rank_chart R v l n k A f D a U e p j g G psi ->
  psi @` (@constant_rank_parameter_domain R v l g a e)=f @` U.
Proof.
move=>hC; pose V:=@constant_rank_parameter_domain R v l g a e.
pose X:=R_n R (v+l).
pose NX:=inner_norm (@euclidean_inner_productP R (v+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (v+l)).
pose i:=@euclidean_first_injection_map R v l.
pose j0:=@euclidean_last_injection_map R v l.
pose q:=@euclidean_last_block_map R v l.
have hchart:=constant_rank_source_chart hC.
apply/seteqP; split=>y.
- move=>[u hu <-].
  have hbox:@euclidean_product_box R v l (g a) e (i u+j0 (q (g a))).
    apply: (@euclidean_product_box_coordinates R v l (g a) e u (q (g a))).2.
    split; first exact hu.
    by rewrite subrr inner_norm0; exact: constant_rank_radius_positive hC.
  exists (G (i u+j0 (q (g a)))).
  + exact (@norm_diffeomorphism_inverse_maps R X X NX NX hNX hNX U
      (@euclidean_product_box R v l (g a) e) g G k hchart _ hbox).
  + exact: esym (constant_rank_section_formula hC hu).
- move=>[x hx <-].
  have hbox:=@norm_diffeomorphism_maps R X X NX NX hNX hNX U
    (@euclidean_product_box R v l (g a) e) g G k hchart x hx.
  exists (p (f x)).
  + by rewrite -(constant_rank_source_prefix hC hx); exact hbox.1.
  + exact: esym (constant_rank_section_factor hC hx).
Qed.
