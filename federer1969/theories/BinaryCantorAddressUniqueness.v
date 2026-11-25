(** Federer (1969), 3.4.4, p. 318: uniqueness
    and consistency of the original finite interval addresses. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  BinaryCantorCodingUP BinaryCantorCodingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_address_point_unique]: the
    original level intervals give unambiguous order correspondence,
    supporting 3.4.4, p. 318. At a common source
    point, equal-length addresses coincide. The sharp sibling
    gap, proved from endpoint laws, excludes different last digits. *)
Theorem binary_original_address_point_unique (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->0<rho ->0<1-2*rho ->
  forall n u v (x:real_line_metric R),size u=n ->size v=n ->
    val (I u) x ->val (I v) x ->u=v.
Proof.
move=>h hRho hGap.
have hUpper:rho<=1 by nra.
elim=>[u v x hu hv hx hy|n ih u v x hu hv hx hy].
- have hU:u=[::] by apply/eqP;rewrite -size_eq0;apply/eqP;exact:hu.
  have hV:v=[::] by apply/eqP;rewrite -size_eq0;apply/eqP;exact:hv.
  by rewrite hU hV.
- case/lastP:u hu hx=>[|u b] hu hx;first by [].
  case/lastP:v hv hy=>[|v c] hv hy;first by [].
  have hU:size u=n by move:hu;rewrite size_rcons=>/succn_inj.
  have hV:size v=n by move:hv;rewrite size_rcons=>/succn_inj.
  have hParentU:val (I u) x:=@binary_original_coding_child_subset R rho J H I a h (ltW hRho) hUpper u b x hx.
  have hParentV:val (I v) x:=@binary_original_coding_child_subset R rho J H I a h (ltW hRho) hUpper v c x hy.
  have hUV:u=v:=ih u v x hU hV hParentU hParentV.
  subst v;clear hu hv.
  have hBits:b=c.
    have hPositive:0<(1-2*rho)*rho^+(size u).
      apply:mulr_gt0 hGap _;by rewrite exprn_gt0.
    case:b c hx hy=>[|][|] hx hy //.
    + exfalso;have hBound:=(@binary_original_coding_sibling_gap R rho J H I a h u x x hy hx).1.
      rewrite subrr in hBound;nra.
    + exfalso;have hBound:=(@binary_original_coding_sibling_gap R rho J H I a h u x x hx hy).1.
      rewrite subrr in hBound;nra.
  by rewrite hBits.
Qed.

(** Source for [binary_original_point_address_exists]: every
    original Cantor point belongs to an original addressed interval
    at every level, 3.4.4, p. 318, by the
    exact original limit and coding laws. *)
Lemma binary_original_point_address_exists (R:realType) (rho:R) J H I a A:
  is_binary_original_coding rho J H I a ->is_special_interval_tree_limit H A ->
  forall (x:real_line_metric R),A x ->forall j,
    exists w,size w=j /\val (I w) x.
Proof.
move=>h hA x hx j.
have [S [hS hxS]]:=(hA x).1 hx j.
have [w [hw hIS]]:=(binary_original_coding_levels h j S).1 hS.
exists w;split;first exact:hw.
by rewrite hIS.
Qed.

(** Source for [binary_original_point_address_step]: the
    original intervals containing a Cantor point form a consistent
    path, supporting the induced correspondence in 3.4.4,
    p. 318. A next-level address extends the unique
    preceding address by one original left/right digit. *)
Lemma binary_original_point_address_step (R:realType) (rho:R) J H I a:
  is_binary_original_coding rho J H I a ->0<rho ->0<1-2*rho ->
  forall n u v (x:real_line_metric R),size u=n ->size v=n.+1 ->
    val (I u) x ->val (I v) x ->exists b,v=rcons u b.
Proof.
move=>h hRho hGap n u v x hu hv hx hy.
have hUpper:rho<=1 by nra.
case/lastP:v hv hy=>[|w b] hv hy;first by [].
have hw:size w=n by move:hv;rewrite size_rcons=>/succn_inj.
have hParent:val (I w) x:=@binary_original_coding_child_subset R rho J H I a h (ltW hRho) hUpper w b x hy.
have hSame:w=u:=@binary_original_address_point_unique R rho J H I a h hRho hGap n w u x hw hu hParent hx.
exists b;by rewrite hSame.
Qed.
