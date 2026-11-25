(** Choice of normal for Federer (1969), 2.10.30, p. 195. Unit normals
    defining the same orthogonal hyperplane differ only by sign. This
    supports independence of the oriented normal used to represent the
    book's unoriented hyperplane. It follows from the project's
    inner-product laws, in arbitrary dimension. Source context and
    inner-product background: UnitNormalGeometry.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm OrthonormalFamilies
  Bilinear UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_normal_same_hyperplane]: supporting
    normal-choice independence of the hyperplane operation
    in 2.10.30, p. 195. The hypothesis
    identifies the whole orthogonal hyperplane, not
    merely a common subset of the two kernels. *)
Theorem unit_normal_same_hyperplane (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (H : set V) (u v : V) :
  @is_unit_normal R V B hB H u -> @is_unit_normal R V B hB H v ->
  v=u \/ v= -u.
Proof.
move=> [hu hHu] [hv hHv].
pose w := normal_foot hB u v.
have hwu : inner_coordinate hB u w=0 := normal_coordinate_foot hB hu v.
have hwv : inner_coordinate hB v w=0 := (hHv w).1 ((hHu w).2 hwu).
have hww : B w w=0.
  change (B w (v-(inner_coordinate hB u v)*:u)=0).
  rewrite (bilBr (inner_bilinear hB)) (bilZr (inner_bilinear hB)).
  change (B w v-(inner_coordinate hB u v)*B w u=0).
  by rewrite -(inner_coordinateE hB v w) -(inner_coordinateE hB u w) hwv hwu mulr0 subrr.
have hw0 : w=0 by apply/eqP; rewrite -(inner_self_eq0 hB) hww eqxx.
have hev : v=(inner_coordinate hB u v)*:u.
  have hh := normal_decomposition hB u v; rewrite -/w hw0 add0r in hh; exact (esym hh).
have hsq : (inner_coordinate hB u v)^+2= 1.
  have hh := hv; rewrite hev (inner_scale_square hB) hu mulr1 in hh; exact hh.
have /orP[hc|hc] : (inner_coordinate hB u v== 1) || (inner_coordinate hB u v== -1).
  by rewrite -sqrf_eq1 hsq eqxx.
- left; by rewrite hev (eqP hc) scale1r.
- right; by rewrite hev (eqP hc) scaleN1r.
Qed.
