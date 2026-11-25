(** Federer (1969), 3.2.31, p. 269: supporting existence
    of a symmetric automorphism with separate large and small
    scales. A local witness proves the independent action laws;
    no global automorphism or implementation is selected. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Hom Bilinear SymmetricEndomorphisms ProjectionScaleAutomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [projection_scale_automorphism_exists]: supporting
    the approximation of the low-rank symmetric map in Federer
    3.2.31, p. 269. A symmetric idempotent splits the space
    into its range and kernel. Prescribe nonzero scales there
    and their reciprocals for the inverse. The witness remains
    local to this opaque existence proof. No finite dimension
    or ordered-field premise is needed for this algebraic step. *)
Theorem projection_scale_automorphism_exists (K:fieldType) (V:lmodType K)
    (B:V->V->K) (hB:@bilinear K V V K^o B)
    (P:Hom V V) (a b:K):
  is_symmetric_endomorphism B (hom_as_linear P) ->
  (forall x,P (P x)= P x) ->a!=0 ->b!=0 ->
  exists T U,@is_projection_scale_automorphism K V B P a b T U.
Proof.
move=>hSym hIdem ha hb.
pose I:Hom V V:=hom_of_linear (linear_id V).
pose T:Hom V V:=a*:P+b*:(I-P).
pose U:Hom V V:=a^-1*:P+b^-1*:(I-P).
have hTE x:T x=a*:P x+b*:(x-P x) by [].
have hUE x:U x=a^-1*:P x+b^-1*:(x-P x) by [].
have hPT x:P (T x)=a*:P x.
  rewrite hTE linearD !linearZ linearB.
  change (a*:P (P x)+b*:(P x-P (P x))=a*:P x).
  by rewrite hIdem subrr scaler0 addr0.
have hPU x:P (U x)=a^-1*:P x.
  rewrite hUE linearD !linearZ linearB.
  change (a^-1*:P (P x)+b^-1*:(P x-P (P x))=a^-1*:P x).
  by rewrite hIdem subrr scaler0 addr0.
have hTMinus x:T x-a*:P x=b*:(x-P x).
  by rewrite hTE addrC addKr.
have hUMinus x:U x-a^-1*:P x=b^-1*:(x-P x).
  by rewrite hUE addrC addKr.
exists T,U; constructor.
- move=>x y; change (B (T x) y=B x (T y)).
  rewrite !hTE (bilDl hB) !(bilZl hB) (bilBl hB)
    (bilDr hB) !(bilZr hB) (bilBr hB).
  change (a*B (P x) y+b*(B x y-B (P x) y)=
    a*B x (P y)+b*(B x y-B x (P y))).
  by rewrite hSym.
- move=>x; rewrite hUE hPT hTMinus !scalerA !mulVf ?ha ?hb // !scale1r.
  by rewrite addrC subrK.
- move=>x; rewrite hTE hPU hUMinus !scalerA !mulfV ?ha ?hb // !scale1r.
  by rewrite addrC subrK.
- move=>x; by rewrite hTE hIdem subrr scaler0 addr0.
- move=>x hx; by rewrite hTE hx scaler0 subr0 add0r.
- move=>x; by rewrite hUE hIdem subrr scaler0 addr0.
- move=>x hx; by rewrite hUE hx scaler0 subr0 add0r.
Qed.
