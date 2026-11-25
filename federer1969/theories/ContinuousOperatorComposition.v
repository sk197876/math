(** Federer (1969), 3.1.11, p. 220:
    composition of continuous linear maps is a
    continuous bilinear operation. The operator spaces
    are arbitrary realizations of the existing specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP NormOperatorNormUP NormDifferentialUP
  NormDifferentialLinear ContinuousOperatorUP NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_operator_composition_exists]:
    the bilinearity of composing linear maps used
    in Federer 3.1.11, p. 220.
    The evaluation identity and norm bound
    characterize a lift of composition through
    the abstract spaces of continuous operators. *)
Theorem continuous_operator_composition_exists (R : realType)
    (X Y Z P Q S : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (ep : Hom P (Hom X Y)) (PN : P->R)
    (eq : Hom Q (Hom Y Z)) (QN : Q->R)
    (es : Hom S (Hom X Z)) (SN : S->R)
    (hP : is_continuous_operator_space NX NY ep PN)
    (hQ : is_continuous_operator_space NY NZ eq QN)
    (hS : is_continuous_operator_space NX NZ es SN) :
  exists C : P->Q->S,
    norm_bounded_bilinear PN QN SN C /\
    forall p q, es (C p q)=hom_comp (eq q) (ep p).
Proof.
have hex (pq : P*Q) : exists s, es s=hom_comp (eq pq.2) (ep pq.1).
  apply: (continuous_operator_surjective hS).
  exact (norm_bounded_linear_compose (continuous_operator_bounded hP pq.1)
    (continuous_operator_bounded hQ pq.2)).
have [c hc] := choice hex.
pose C p q := c (p,q).
have hC p q : es (C p q)=hom_comp (eq q) (ep p) := hc (p,q).
exists C; split; last exact hC.
split.
- split.
  + move=> q a p p'; apply: (continuous_operator_injective hS).
    change (es (C (a*:p+p') q)=es (a*:C p q+C p' q)).
    rewrite (hom_linear es) !hC (hom_linear ep).
    exact: hom_postcompose_linear.
  + move=> p a q q'; apply: (continuous_operator_injective hS).
    change (es (C p (a*:q+q'))=es (a*:C p q+C p q')).
    rewrite (hom_linear es) !hC (hom_linear eq).
    exact: hom_precompose_linear.
- exists 1; split; first exact: ler01.
  move=> p q; rewrite mul1r.
  have hp := norm_operator_nonnegative (continuous_operator_norm_laws hP p).
  have hq := norm_operator_nonnegative (continuous_operator_norm_laws hQ q).
  apply: (norm_operator_least (continuous_operator_norm_laws hS (C p q))
    (mulr_ge0 hp hq))=>x.
  rewrite hC hom_compE.
  have h := le_trans (norm_operator_bound (continuous_operator_norm_laws hQ q) (ep p x))
    (ler_wpM2l hq (norm_operator_bound (continuous_operator_norm_laws hP p) x)).
  have he : QN q*(PN p*NX x)=(PN p*QN q)*NX x by ring.
  by rewrite he in h.
Qed.
