(** Federer (1969), 3.4.12, p. 339: the prescribed
    complex prefix slice uses a product of open coordinate balls.
    Apply the existing real norm interior laws to the original
    complex block maps and their checked isometric inclusions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases
  FiniteCoordinates HolomorphicCoordinateNorm RealNormUP NormDifferentialUP HolomorphicLinear
  NormFiniteLinearBound NormOpenDomainLaws NormLinearDomainLaws FieldBlockLinearMaps ComplexBlockNorms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Box.
Variable R:realType.
Variables v l:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space C (v+l)).
Local Notation V:=(coordinate_space C v).
Local Notation W:=(coordinate_space C l).
Local Notation NX:=(@holomorphic_coordinate_norm R (v+l)).
Local Notation NV:=(@holomorphic_coordinate_norm R v).
Local Notation NW:=(@holomorphic_coordinate_norm R l).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (v+l))).
Local Notation hNV:=(complex_norm_real (@holomorphic_coordinate_norm_laws R v)).
Local Notation hNW:=(complex_norm_real (@holomorphic_coordinate_norm_laws R l)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation VR:=(restricted_space (ComplexScalars.embed R) V).
Local Notation WR:=(restricted_space (ComplexScalars.embed R) W).
Local Notation p:=(@field_first_block_map C v l).
Local Notation q:=(@field_last_block_map C v l).
Local Notation i:=(@field_first_injection_map C v l).
Local Notation j:=(@field_last_injection_map C v l).

(** Source for [complex_product_box]: the convex product
    neighbourhood V times W in Federer 3.1.18, p. 229, using open
    balls in both coordinate factors. Empty factors are retained. *)
Definition complex_product_box (c:X) (e:R):set X :=
  fun x=>NV (p x-p c)<e /\ NW (q x-q c)<e.

(** Source for [complex_product_box_center]: the product contains
    its centre, supporting the neighbourhood choice in 3.1.18, p. 229. *)
Lemma complex_product_box_center c e : 0<e -> complex_product_box c e c.
Proof. move=>he; rewrite /complex_product_box !subrr !(real_seminorm_zero (complex_norm_real (@holomorphic_coordinate_norm_laws R v)).1) !(real_seminorm_zero (complex_norm_real (@holomorphic_coordinate_norm_laws R l)).1); by split. Qed.

(** Source for [complex_product_box_open]: the product of the
    two open coordinate balls is open, supporting 3.1.18, p. 229. *)
Lemma complex_product_box_open c e x : complex_product_box c e x ->
  @norm_domain_interior R XR NX (complex_product_box c e) x.
Proof.
move=>[hx hy].
have hp:=@norm_finite_linear_bounded R XR VR NX NV hNX hNV (v+l+(v+l))
  (ordered_real_basis (@coordinate_basis C (v+l))) (ordered_real_basisP (@coordinate_basisP C (v+l))) (complex_hom_real p).
have hq:=@norm_finite_linear_bounded R XR WR NX NW hNX hNW (v+l+(v+l))
  (ordered_real_basis (@coordinate_basis C (v+l))) (ordered_real_basisP (@coordinate_basisP C (v+l))) (complex_hom_real q).
have hpx:=@norm_open_ball_domain_interior R VR NV hNV (p c) e (p x) hx.
have hqx:=@norm_open_ball_domain_interior R WR NW hNW (q c) e (q x) hy.
have hP:=@norm_bounded_linear_preimage_interior R XR VR NX NV hNX (complex_hom_real p)
  (fun u=>NV (u-p c)<e) x hp hpx.
have hQ:=@norm_bounded_linear_preimage_interior R XR WR NX NW hNX (complex_hom_real q)
  (fun w=>NW (w-q c)<e) x hq hqx.
exact: norm_domain_intersection_interior hP hQ.
Qed.

(** Source for [complex_product_box_coordinates]: exact membership
    under the product parametrisation (u,w), supporting the W-fibre
    argument in Federer 3.1.18, p. 230. *)
Lemma complex_product_box_coordinates c e u w :
  complex_product_box c e (i u+j w) <-> NV (u-p c)<e /\ NW (w-q c)<e.
Proof.
rewrite /complex_product_box !linearD /=.
rewrite field_first_block_injectionK field_first_block_last_injection
  field_last_block_first_injection field_last_block_injectionK addr0 add0r.
by [].
Qed.

(** Source for [complex_product_box_fits]: a product of convex
    neighbourhoods can be chosen inside the open image of g, Federer
    3.1.18, p. 229. This form states the actual inclusion, not a
    topological existence premise for later proofs. *)
Lemma complex_product_box_fits (T:X->Prop) c :
  @norm_domain_interior R XR NX T c -> exists e:R, 0<e /\
    forall x, complex_product_box c e x -> T x.
Proof.
move=>[r [hr hball]].
exists (r/3); split; first by rewrite divr_gt0 // ltr0n.
move=>x [hx hy].
have hs:=@complex_product_box_in_ball R v l c x r hr hx hy.
have hh:=hball (x-c) hs.
by rewrite (addrC c (x-c)) subrK in hh.
Qed.
End Box.
