(** Federer (1969), 3.1.11, p. 219:
    the printed g_v estimate for the second-difference
    remainder, using the derivative bound on a convex ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals lra ring.
From Federer Require Import Hom RealNormUP InnerConvex NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialSubtraction
  NormClassOneNormalization NormDifferentialConvexBound NormSecondDifferenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_second_difference_estimate]: the bound
    |g_v(u)| <= 2 epsilon (|u|+|v|)^2 in Federer
    3.1.11, p. 219. The assumptions are precisely
    the local derivative field and its first-order operator
    remainder used at this stage of the printed proof.
    They are discharged from the second differential later. *)
Theorem norm_second_difference_estimate (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (f : X->Y) (D : X->Hom X Y)
    (B : Hom X (Hom X Y)) (e r : R) :
  0<=e -> 0<r ->
  (forall x, NX x< 2*r -> has_norm_differential NX NY A f x (D x)) ->
  (forall x, NX x< 2*r -> forall w,
    NY ((D x-D 0-B x) w)<=e*NX x*NX w) ->
  (forall v, norm_bounded_linear NX NY (B v)) ->
  forall u v, NX u<r -> NX v<r ->
    NY (norm_second_difference f 0 u v-B v u)<= 2*e*(NX u+NX v)^+2.
Proof.
move=> he hr hD hrem hB u v hu hv.
pose V := [set x | NX x<r].
pose U := [set x | NX x<=NX u].
pose g := fun x=>((f (v+x)-f v)-(f x-f 0))-B v x.
have hu0 := real_seminorm_nonnegative hNX.1 u.
have hv0 := real_seminorm_nonnegative hNX.1 v.
have hVint x : V x -> norm_domain_interior NX V x.
  move=> hx; exists (r-NX x); split; first by rewrite subr_gt0.
  move=> h hh.
  have ht := real_seminorm_triangle hNX.1 x h.
  change (is_true (NX (x+h)<r)); lra.
have h2r : 2*r=r+r by rewrite mulr_natl mulr2n.
have hsmall x : V x -> NX x< 2*r.
  move=> hx; change (is_true (NX x<r)) in hx.
  rewrite h2r; apply: lt_trans hx _; by rewrite ltrDl.
have hsum x : V x -> NX (v+x)< 2*r.
  move=> hx; have ht := real_seminorm_triangle hNX.1 v x.
  change (is_true (NX x<r)) in hx.
  rewrite h2r; exact: le_lt_trans ht (ltrD hv hx).
have hVA : V `<=` A.
  move=> x hx; exact: (@norm_domain_interior_member R X NX hNX A x
    (norm_differential_interior (hD x (hsmall x hx)))).
have hVvA : V `<=` [set x | A (v+x)].
  move=> x hx; exact: (@norm_domain_interior_member R X NX hNX A (v+x)
    (norm_differential_interior (hD (v+x) (hsum x hx)))).
have hg x : V x ->
    has_norm_differential NX NY V g x (D (v+x)-D x-B v).
  move=> hx.
  have h1 := @norm_differential_translate R X Y NX NY A f v x
    (f v) (D (v+x)) (hD (v+x) (hsum x hx)).
  have h1V := norm_differential_restrict hVvA (hVint x hx) h1.
  have h0 : has_norm_differential NX NY A f (0+x) (D x).
    rewrite add0r; exact: hD x (hsmall x hx).
  have h0t := @norm_differential_translate R X Y NX NY A f 0 x
    (f 0) (D x) h0.
  have heA : (fun z : X=>A (0+z))=A.
    by apply: funext=> z; rewrite add0r.
  have hef : (fun z : X=>f (0+z)-f 0)=(fun z=>f z-f 0).
    by apply: funext=> z; rewrite add0r.
  rewrite heA hef in h0t.
  have h0V := norm_differential_restrict hVA (hVint x hx) h0t.
  have hdif := norm_differential_subtract hNX hNY h1V h0V.
  have hlin := norm_differential_linear hNX hNY (hVint x hx) (hB v).
  have hh := norm_differential_subtract hNX hNY hdif hlin.
  exact hh.
have hconv : is_inner_convex U.
  move=> x y hx hy t ht ht1.
  have h1t : 0<= 1-t by rewrite subr_ge0.
  apply: le_trans (real_seminorm_triangle hNX.1 _ _) _.
  rewrite !(real_seminorm_scale hNX.1) (ger0_norm h1t) (ger0_norm ht).
  have hh := lerD (ler_wpM2l h1t hx) (ler_wpM2l ht hy).
  by rewrite -mulrDl subrK mul1r in hh.
have hM : 0<= 2*e*(NX u+NX v) by apply: mulr_ge0; [nra|exact: addr_ge0].
have hLip := @norm_differential_convex_bound R X Y NX NY hNX hNY
  V U g (2*e*(NX u+NX v)) hconv hM.
have hder : forall x, U x -> exists L : Hom X Y,
    has_norm_differential NX NY V g x L /\
    forall w, NY (L w)<= 2*e*(NX u+NX v)*NX w.
  move=> x hx.
  change (is_true (NX x<=NX u)) in hx.
  have hxV : V x := le_lt_trans hx hu.
  exists (D (v+x)-D x-B v); split; first exact: hg x hxV.
  move=> w.
  have hid : D (v+x)-D x-B v=
      (D (v+x)-D 0-B (v+x))-(D x-D 0-B x).
    by rewrite linear_remainder_difference_identity (linearD B v x) /= addrK.
  rewrite hid.
  have htri := real_seminorm_triangle hNY.1
    ((D (v+x)-D 0-B (v+x)) w) (-((D x-D 0-B x) w)).
  rewrite (real_seminorm_negate hNY.1) in htri.
  apply: le_trans htri _.
  have hb := lerD (hrem (v+x) (hsum x hxV) w)
    (hrem x (hsmall x hxV) w).
  apply: le_trans hb _.
  have ht := real_seminorm_triangle hNX.1 v x.
  have hw0 := real_seminorm_nonnegative hNX.1 w.
  have hx0 := real_seminorm_nonnegative hNX.1 x.
  have hc : e*NX (v+x)+e*NX x<= 2*e*(NX u+NX v) by nra.
  have hh := ler_wpM2r hw0 hc.
  by rewrite mulrDl in hh.
have hzero : U 0.
  change (is_true (NX 0<=NX u)).
  by rewrite (real_seminorm_zero hNX.1).
have hh := hLip hder u 0 (lexx _) hzero.
have hg0 : g 0= 0 by rewrite /g addr0 !subrr linear0 subr0.
rewrite hg0 subr0 subr0 in hh.
have hgu : g u=norm_second_difference f 0 u v-B v u.
  rewrite /g /norm_second_difference !add0r (addrC v u) opprB !addrA.
  by rewrite (addrAC (f (u+v)-f v) (f 0) (-f u))
    (addrAC (f (u+v)) (-f v) (-f u)).
rewrite hgu in hh.
apply: le_trans hh _.
have hs : 0<=NX u+NX v by exact: addr_ge0.
have huS : NX u<=NX u+NX v by lra.
have he2 : 0<= 2*e by nra.
have hc := ler_wpM2l (mulr_ge0 he2 hs) huS.
by rewrite expr2 mulrA.
Qed.
