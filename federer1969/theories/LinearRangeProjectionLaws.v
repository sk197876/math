(** Federer (1969), 3.1.18, pp. 229–230: consequences of the
    orthogonal projection onto the range of Df(a). *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP GrassmannAbbreviations
  LinearRangeProjectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Laws.
Variable R:realType.
Variables X Y:lmodType R.
Variable C:Y->Y->R.
Variable L:Hom X Y.
Variable v:nat.
Variables (p:{linear Y->R_n R v}) (j:{linear R_n R v->Y}).
Hypothesis hP:is_linear_range_projection C L p j.

(** Source for [range_projection_composition_surjective]: p Df(a)
    maps onto R^v, supporting the source coordinates in 3.1.18, p. 229. *)
Lemma range_projection_composition_surjective u : exists x, p (L x)=u.
Proof.
have [x hx] := (range_projection_image hP (j u)).1 (ex_intro _ u erefl).
exists x; by rewrite hx (range_projection_cancel hP).
Qed.

(** Source for [range_projection_reconstruct]: p* p is identity on
    image Df(a), supporting the identities in 3.1.18, p. 230. *)
Lemma range_projection_reconstruct y : (exists x, L x=y) -> j (p y)=y.
Proof.
move=>hy; have [u <-] := (range_projection_image hP y).2 hy.
by rewrite (range_projection_cancel hP).
Qed.

(** Source for [range_projection_kernel_at_base]: ker(p Df(a))=
    ker Df(a), stated in Federer 3.1.18, p. 229. *)
Lemma range_projection_kernel_at_base x : p (L x)=0 -> L x=0.
Proof.
move=>hx; have hh:=range_projection_reconstruct (ex_intro _ x erefl).
by rewrite hx linear0 in hh; exact: esym hh.
Qed.
End Laws.
