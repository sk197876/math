(** Federer (1969), 4.1.6, p. 352: in degree
    zero, the exterior derivative is the original
    norm differential under A^0(V,W)=W and
    A^1(V,W)=Hom(V,W). Both identifications are
    the actual earlier linear isomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  AlternatingForms AlternatingZero OneFormIdentification
  ExteriorDifferentialUP ExteriorDifferentialNormBound ExteriorDerivativeUP
  AlternatingFormNormUP AlternatingFormZeroNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_differential_zero_value]: the
    signed definition has exactly the ordinary
    first-differential values in degree zero,
    Federer 4.1.6, p. 352. *)
Theorem exterior_differential_zero_value (K:fieldType) (V W:lmodType K) (L:Hom V W):
  is_exterior_differential_value
    (hom_comp (hom_of_linear (@zero_form K V W)) L) (one_form L).
Proof.
move=>t; rewrite exterior_differential_trace_tuple_values big_ord1 expr0 scale1r.
have hT:t=[tuple tnth t ord0].
  apply:eq_from_tnth=>i; by rewrite (ord1 i).
rewrite hT one_formE hom_compE.
by rewrite zero_formE.
Qed.

(** Source for [exterior_derivative_zero_degree]: the
    printed interpretation d phi=D phi,
    Federer 4.1.6, p. 352, uses the
    actual induced norm and the actual differential. *)
Theorem exterior_derivative_zero_degree (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) (hNW:is_real_norm NW)
    (P:A_m V W 0->R) (hP:is_alternating_form_norm NV NW P)
    (U:V->Prop) (f:V->W) a (L:Hom V W):
  has_norm_differential NV NW U f a L ->
  has_exterior_derivative NV P U (fun x=>@zero_form R V W (f x)) a (one_form L).
Proof.
move=>hL.
have hZ:norm_bounded_linear NW P (hom_of_linear (@zero_form R V W)).
  exists 1; split; first exact:ler01.
  move=>w; rewrite mul1r (alternating_form_zero_norm hNV hNW hP) zero_formK; exact:lexx.
exists (hom_comp (hom_of_linear (@zero_form R V W)) L); split.
- exact:(norm_differential_postcompose hNV hL hZ).
- exact:exterior_differential_zero_value.
Qed.
