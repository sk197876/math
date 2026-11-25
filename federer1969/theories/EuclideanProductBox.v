(** Federer (1969), 3.1.18, p. 229: the product V times W of
    convex open neighbourhoods, represented under the standard
    identification with R^(v+l). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  NormFiniteLinearBound NormOpenDomainLaws NormLinearDomainLaws
  EuclideanBlockLinearMaps EuclideanBlockNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Box.
Variable R:realType.
Variables v l:nat.
Local Notation X:=(R_n R (v+l)).
Local Notation V:=(R_n R v).
Local Notation W:=(R_n R l).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (v+l))).
Local Notation NV:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NW:=(inner_norm (@euclidean_inner_productP R l)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (v+l))).
Local Notation hNV:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNW:=(inner_norm_real_norm (@euclidean_inner_productP R l)).
Local Notation p:=(@euclidean_first_block_map R v l).
Local Notation q:=(@euclidean_last_block_map R v l).
Local Notation i:=(@euclidean_first_injection_map R v l).
Local Notation j:=(@euclidean_last_injection_map R v l).

(** Source for [euclidean_product_box]: the convex product
    neighbourhood V times W in Federer 3.1.18, p. 229, using open
    balls in both coordinate factors. Empty factors are retained. *)
Definition euclidean_product_box (c:X) (e:R):set X :=
  fun x=>NV (p x-p c)<e /\ NW (q x-q c)<e.

(** Source for [euclidean_product_box_center]: the product contains
    its centre, supporting the neighbourhood choice in 3.1.18, p. 229. *)
Lemma euclidean_product_box_center c e : 0<e -> euclidean_product_box c e c.
Proof. move=>he; rewrite /euclidean_product_box !subrr !inner_norm0; by split. Qed.

(** Source for [euclidean_product_box_open]: the product of the
    two open coordinate balls is open, supporting 3.1.18, p. 229. *)
Lemma euclidean_product_box_open c e x : euclidean_product_box c e x ->
  norm_domain_interior NX (euclidean_product_box c e) x.
Proof.
move=>[hx hy].
have hp:=@norm_finite_linear_bounded R X V NX NV hNX hNV (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) p.
have hq:=@norm_finite_linear_bounded R X W NX NW hNX hNW (v+l)
  (@coordinate_basis R (v+l)) (@coordinate_basisP R (v+l)) q.
have hpx:=@norm_open_ball_domain_interior R V NV hNV (p c) e (p x) hx.
have hqx:=@norm_open_ball_domain_interior R W NW hNW (q c) e (q x) hy.
have hP:=@norm_bounded_linear_preimage_interior R X V NX NV hNX p
  (fun u=>NV (u-p c)<e) x hp hpx.
have hQ:=@norm_bounded_linear_preimage_interior R X W NX NW hNX q
  (fun w=>NW (w-q c)<e) x hq hqx.
exact: norm_domain_intersection_interior hP hQ.
Qed.

(** Source for [euclidean_product_box_coordinates]: exact membership
    under the product parametrisation (u,w), supporting the W-fibre
    argument in Federer 3.1.18, p. 230. *)
Lemma euclidean_product_box_coordinates c e u w :
  euclidean_product_box c e (i u+j w) <-> NV (u-p c)<e /\ NW (w-q c)<e.
Proof.
rewrite /euclidean_product_box !linearD /=.
rewrite euclidean_first_block_injectionK euclidean_first_block_last_injection
  euclidean_last_block_first_injection euclidean_last_block_injectionK addr0 add0r.
by [].
Qed.

(** Source for [euclidean_product_box_fits]: a product of convex
    neighbourhoods can be chosen inside the open image of g, Federer
    3.1.18, p. 229. This form states the actual inclusion, not a
    topological existence premise for later proofs. *)
Lemma euclidean_product_box_fits (T:X->Prop) c :
  norm_domain_interior NX T c -> exists e:R, 0<e /\
    forall x, euclidean_product_box c e x -> T x.
Proof.
move=>[r [hr hball]].
exists (r/3); split; first by rewrite divr_gt0 // ltr0n.
move=>x [hx hy].
have hs:=@euclidean_product_box_in_ball R v l c x r hr hx hy.
have hh:=hball (x-c) hs.
by rewrite (addrC c (x-c)) subrK in hh.
Qed.
End Box.
