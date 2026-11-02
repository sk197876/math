(** Federer (1969), 3.1.20, p. 232, interpolated local formula.
    Its image is T intersect B, as corrected by the erratum p. 4,
    book p. 232 lines 14–15; it need not lie in the old domain W. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  NormRegularityBilinear NormClassZeroComposition NormClassZeroTopology NormLinearDomainLaws
  InnerConvex LocalRetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Blend.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables (B W T:set X) (V:set Y) (f:X->X) (phi:X->Y) (psi:Y->X) (u:X->R^o) (k:nat).
Hypothesis hpartial:is_partial_neighbourhood_retraction hNX B W f k.
Hypothesis hphi:norm_class hNX hNY T phi k.
Hypothesis hpsi:norm_class hNY hNX V psi k.
Hypothesis hphiV:forall x, T x -> V (phi x).
Hypothesis him:psi @` V=B `&` T.
Hypothesis hcan:forall y, V y -> phi (psi y)=y.
Hypothesis hconv:is_inner_convex V.
Hypothesis hu:norm_class hNX (scalar_absolute_value_norm R) (fun _=>True) u k.
Hypothesis hrange:forall x, 0<=u x<= 1.

(** Source for [retraction_blend_domain]: the actual domain of
    rho in Federer 3.1.20, p. 232, with the old map's domain
    included explicitly in its inverse image of T. *)
Definition retraction_blend_domain := fun x=>W x /\ T x /\ T (f x).

(** Source for [retraction_coordinate_blend]: the convex combination
    (1-u_s) phi f_(i-1)+u_s phi, Federer 3.1.20, p. 232. *)
Definition retraction_coordinate_blend x := (1-u x)*:phi (f x)+(u x)*:phi x.

(** Source for [retraction_blend]: rho is psi composed with the
    interpolated coordinates, Federer 3.1.20, p. 232. Its laws
    below prove the corrected target T intersect B. *)
Definition retraction_blend x := psi (retraction_coordinate_blend x).

(** Source for [retraction_coordinate_blend_range]: convexity
    keeps the interpolated coordinates inside V, supporting the
    displayed formula in Federer 3.1.20, p. 232. *)
Lemma retraction_coordinate_blend_range x : retraction_blend_domain x ->
  V (retraction_coordinate_blend x).
Proof.
move=>[hw [ht hft]].
have /andP [hu0 hu1]:=hrange x.
exact (@hconv (phi (f x)) (phi x) (@hphiV (f x) hft) (@hphiV x ht)
  (u x) hu0 hu1).
Qed.

(** Source for [retraction_blend_class]: the interpolated map rho
    has class k, Federer 3.1.20, p. 232. All operations are
    performed on its actual open composite domain. *)
Lemma retraction_blend_class : norm_class hNX hNX retraction_blend_domain retraction_blend k.
Proof.
pose D:=retraction_blend_domain.
have hf:=partial_neighbourhood_retraction_class hpartial.
have hopenD x (hx:D x):norm_domain_interior NX D x.
  have hTW:=@norm_class_zero_composite_interior R X X Y NX NX NY W T f phi
    (norm_class_continuous hf) (norm_class_continuous hphi) x (conj hx.1 hx.2.2).
  have hTint:=norm_class_continuous hphi.
  have hi:=norm_domain_intersection_interior hTW (@hTint x hx.2.1).1.
  have [r [hr hball]]:=hi.
  exists r; split=>// h hh.
  have [[hW hTf] hT]:=hball h hh; exact: conj hW (conj hT hTf).
have hfD:=@norm_class_open_restriction R X X NX NX hNX hNX W D f k
  (fun x hx=>hx.1) hopenD hf.
have hphiD:=@norm_class_open_restriction R X Y NX NY hNX hNY T D phi k
  (fun x hx=>hx.2.1) hopenD hphi.
have hphif:=@norm_class_compose_on R X X Y NX NX NY hNX hNX hNY D T f phi k
  (fun x hx=>hx.2.2) hfD hphi.
have huD:=@norm_class_open_restriction R X R^o NX (fun t:R^o=>`|t|) hNX
  (scalar_absolute_value_norm R) (fun _=>True) D u k (fun _ _=>I) hopenD hu.
have hc:=@norm_class_constant R X R^o NX (fun t:R^o=>`|t|) hNX
  (scalar_absolute_value_norm R) D 1 k hopenD.
have hone:=norm_class_subtract hc huD.
have hb:=norm_class_add (norm_class_scalar_product hone hphif)
  (norm_class_scalar_product huD hphiD).
exact (@norm_class_compose_on R X Y X NX NY NX hNX hNY hNX D V
  retraction_coordinate_blend psi k retraction_coordinate_blend_range hb hpsi).
Qed.

(** Source for [retraction_blend_range]: rho takes values in
    T intersect B, Federer 3.1.20, p. 232, erratum p. 4,
    book p. 232 line 14. *)
Lemma retraction_blend_range x : retraction_blend_domain x -> B (retraction_blend x) /\ T (retraction_blend x).
Proof.
move=>hx; change ((B `&` T) (psi (retraction_coordinate_blend x))).
rewrite -him.
by exists (retraction_coordinate_blend x); first exact: retraction_coordinate_blend_range.
Qed.

(** Source for [retraction_blend_chart_inverse]: psi phi fixes
    B intersect T, supporting the patch identities in Federer
    3.1.20, p. 232. *)
Lemma retraction_blend_chart_inverse x : B x -> T x -> psi (phi x)=x.
Proof.
move=>hbx htx.
have hi:(psi @` V) x by rewrite him; split.
have [y hy <-]:=hi; by rewrite hcan.
Qed.

(** Source for [retraction_blend_fixed]: rho fixes B intersect
    its domain, Federer 3.1.20, p. 232, erratum p. 4,
    book p. 232 line 15. *)
Lemma retraction_blend_fixed x : B x -> retraction_blend_domain x -> retraction_blend x=x.
Proof.
move=>hbx [hw [ht hft]].
have hfx:=@partial_neighbourhood_retraction_fixed R X NX hNX B W f k hpartial x hbx hw.
rewrite /retraction_blend /retraction_coordinate_blend hfx -scalerDl subrK scale1r.
exact: retraction_blend_chart_inverse.
Qed.

(** Source for [retraction_blend_old]: rho agrees with the old
    map where u_s=0, the first patch identity in Federer 3.1.20,
    p. 232. *)
Lemma retraction_blend_old x : retraction_blend_domain x -> u x=0 -> retraction_blend x=f x.
Proof.
move=>[hw [ht hft]] hu0.
rewrite /retraction_blend /retraction_coordinate_blend hu0 subr0 scale1r scale0r addr0.
apply: retraction_blend_chart_inverse=>//.
exact (@partial_neighbourhood_retraction_range R X NX hNX B W f k hpartial x hw).
Qed.

(** Source for [retraction_blend_new]: rho agrees with the new
    local coordinate retraction where u_s = 1, the second patch
    identity in Federer 3.1.20, p. 232. *)
Lemma retraction_blend_new x : u x = 1 -> retraction_blend x=psi (phi x).
Proof. move=>hu1; by rewrite /retraction_blend /retraction_coordinate_blend hu1 subrr scale0r scale1r add0r. Qed.
End Blend.
