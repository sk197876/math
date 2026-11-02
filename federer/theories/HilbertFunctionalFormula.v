(** Federer (1969), 1.7.13, p. 37: the explicit vector u=|a-c|^-2(a-c)
    represents f when f(a)= 1, f(c)= 0, and a-c is orthogonal to ker(f).
    This is the algebraic last step of the printed proof, independent of the
    nearest-point construction. Source context: HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  HilbertFunctionalUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [hilbert_functional_residual_formula]: Federer
    1.7.13, p. 37, the last two displays: v-f(v)(a-c)
    lies in ker(f), hence orthogonality yields the representation
    by |a-c|^-2(a-c). *)
Theorem hilbert_functional_residual_formula (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> R^o})
    a c (ha : f a= 1) (hc : f c= 0)
    (ho : forall x, f x= 0 -> B (a-c) x= 0) :
    is_hilbert_functional_vector B f ((inner_norm hB (a-c)^+2)^-1 *: (a-c)).
Proof.
have hr : f (a-c)= 1 by rewrite linearB ha hc subr0.
have hr0 : a-c != 0.
  apply/eqP=> hz; rewrite hz linear0 in hr.
  by move: hr; apply/eqP; rewrite eq_sym oner_eq0.
have hrr : B (a-c) (a-c) != 0 by rewrite (inner_self_eq0 hB).
move=> v.
have hk : f (v-f v *: (a-c))= 0.
  rewrite linearB linearZ hr.
  change (f v - f v * 1 = 0 :> R); by rewrite mulr1 subrr.
have hh := ho _ hk.
rewrite (bilBr (inner_bilinear hB)) (bilZr (inner_bilinear hB)) in hh.
change (B (a-c) v - f v * B (a-c) (a-c)= 0) in hh.
have he : B (a-c) v = f v * B (a-c) (a-c).
  apply/eqP; by rewrite -subr_eq0 hh eqxx.
rewrite (bilZl (inner_bilinear hB)) inner_norm_sqr.
change (f v = (B (a-c) (a-c))^-1 * B (a-c) v).
by rewrite he mulrCA mulVf // mulr1.
Qed.
