(** Federer (1969), 3.1.23, p. 237: projection
    preservation and the exact local straightening equation. *)
From mathcomp Require Import all_boot all_algebra classical_sets.
From Federer Require Import Hom Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [graph_correction_projection]: p composed with f
    equals p, Federer 3.1.23, p. 237. The
    correction lies in ker p by p j= id and p psi= id.
    This remains valid for every cutoff value. *)
Lemma graph_correction_projection (R:fieldType) (X Z:lmodType R)
    (P:Hom X Z) (J:Hom Z X) (psi G:Z->X) b x c :
  cancel J P -> P (psi (P x))= P x ->
  (forall z,G z= J z-psi z+(b-J (P b))) ->
  P (x+c*:G (P x))= P x.
Proof.
move=>hPJ hpsi hG.
have hzero:P (G (P x))= 0.
  by rewrite hG (linD (hom_linear P)) !(linB (hom_linear P)) !hPJ hpsi !subrr ?addr0.
by rewrite (linD (hom_linear P)) (linZ (hom_linear P)) hzero scaler0 addr0.
Qed.

(** Source for [graph_correction_plane_equivalence]: the exact
    equality of B and the inverse image of the affine
    tangent plane inside the inner ball, Federer 3.1.23,
    pp. 236–237. Where the cutoff is one, the
    preserved projection identifies the parameter of any plane
    point, forcing x= psi[p(x)]. No tangent formula is assumed. *)
Lemma graph_correction_plane_equivalence (R:fieldType) (X Z:lmodType R)
    (B T:X->Prop) (V:Z->Prop) (P:Hom X Z) (J:Hom Z X)
    (psi G:Z->X) (F:X->X) b x :
  cancel J P -> V (P x) -> T x ->
  (forall z,V z -> P (psi z)= z) ->
  (forall z,V z -> B (psi z)) ->
  (forall z,B z -> T z -> psi (P z)= z) ->
  (forall z,G z= J z-psi z+(b-J (P b))) ->
  F x= x+G (P x) -> (B x <-> range J (F x-b)).
Proof.
move=>hPJ hxV hxT hcan hrange hinv hG hF.
have hproj:P (F x)= P x.
  rewrite hF; have hh:= @graph_correction_projection R X Z P J psi G b x 1 hPJ (hcan _ hxV) hG.
  by rewrite scale1r in hh.
have hplane:G (P x)+psi (P x)-b= J (P x-P b).
  rewrite hG (linB (hom_linear J)) [J (P x)-psi (P x)+(b-J (P b))+psi (P x)]addrAC subrK.
  by rewrite addrA [J (P x)+b-J (P b)]addrAC addrK.
split.
- move=>hxB; exists (P x-P b); first exact Logic.I.
  symmetry; have hh:=hplane; rewrite (hinv x hxB hxT) in hh.
  rewrite hF [x+G (P x)]addrC; exact hh.
- move=>[z _ hz].
  have hzP:= congr1 P hz.
  rewrite hPJ (linB (hom_linear P)) hproj in hzP.
  have heq0:F x-b= G (P x)+psi (P x)-b.
    rewrite -hz hzP; exact: esym hplane.
  have heq1:F x= G (P x)+psi (P x):= addIr (-b) heq0.
  rewrite hF [x+G (P x)]addrC in heq1.
  have hxpsi:x= psi (P x):= addrI (G (P x)) heq1.
  rewrite hxpsi; exact (hrange _ hxV).
Qed.
