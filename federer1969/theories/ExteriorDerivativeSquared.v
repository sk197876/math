(** Federer (1969), 4.1.6, p. 353: d(d phi)=0
    for twice differentiable forms. The exact original
    recursive second differential supplies symmetry;
    no continuity of the second derivative, whole-target
    separability or completeness is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormDifferentialFiniteCalculus ContinuousMultilinearUP ContinuousMultilinearOne
  MultilinearSuccessorArguments NormHigherDifferentialUP NormHigherDifferentialFirst
  NormHigherDifferentialFields NormHigherDifferentialUnique NormHigherDifferential
  NormSecondDifferential GrassmannAbbreviations AlternatingForms AlternatingFormNormUP
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDifferentialOperator
  ExteriorDifferentialSecondZero ExteriorDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ExteriorDerivativeSquared.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable W:lmodType R.
Local Notation X:=(R_n R n).
Variables (NV:X->R) (NW:W->R).
Hypothesis hNV:is_real_norm NV.
Hypothesis hNW:is_real_norm NW.
Variable m:nat.
Variables (P:A_m X W m->R) (Q:A_m X W m.+1->R).
Hypothesis hNP:is_real_norm P.
Hypothesis hP:is_alternating_form_norm NV NW P.
Hypothesis hQ:is_alternating_form_norm NV NW Q.
Variable Z:nat->lmodType R.
Variable evaluation:forall k,{ffun 'I_k->X}->Hom (Z k) (A_m X W m).
Variable ZN:forall k,Z k->R.
Hypothesis hZ:forall k,is_continuous_multilinear_space NV P (@evaluation k) (@ZN k).
Variable U:X->Prop.
Variable phi:X->A_m X W m.
Local Notation HD:=(@has_norm_higher_differential R X (A_m X W m) NV Z evaluation ZN U phi).
Local Notation J:=(@continuous_multilinear_one_evaluation R X (A_m X W m)
  (Z 1%N) NV P (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N)).
Local Notation T:=(hom_comp (@exterior_differential_map R h2 n W m) J).

(** Source for [exterior_derivative_squared_at]: the
    double-coordinate cancellation with the actual
    first differential field, Federer 4.1.6,
    p. 353. Twice differentiability at the point
    is sufficient for the asserted derivative there. *)
Theorem exterior_derivative_squared_at (F:X->Z 1%N) a (z:Z 2%N):
  (forall x,U x->HD 1%N x (F x))->HD 2%N a z->
  has_exterior_derivative NV Q U (fun x=>T (F x)) a 0.
Proof.
move=>hF hSecond.
have [L [hL hValues]]:=norm_higher_differential_field_step_elim hNV hF hSecond.
have hSym:forall u v,(hom_comp J L) u v=(hom_comp J L) v u.
  move=>u v; rewrite !hom_compE.
  change (@evaluation 1%N [ffun i:'I_1=>v] (L u)=
    @evaluation 1%N [ffun i:'I_1=>u] (L v)).
  rewrite !hValues.
  exact:(@norm_second_differential_symmetric R X (A_m X W m) NV P hNV hNP
    Z evaluation ZN hZ U phi a z hSecond v u).
have hBound:norm_bounded_linear (@ZN 1%N) Q T.
  exact:(@exterior_differential_operator_bounded R h2 n W NV NW hNV hNW
    m P Q hP hQ (Z 1%N) (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N)).
have hDerivative:=norm_differential_postcompose hNV hL hBound.
have hAssociative:hom_comp T L=
    hom_comp (@exterior_differential_map R h2 n W m) (hom_comp J L).
  apply:hom_ext=>v; by rewrite !hom_compE.
have hZero:=@exterior_differential_symmetric_second_zero R h2 n W m (hom_comp J L) hSym.
rewrite -hAssociative in hZero.
exists (hom_comp T L); split; first exact:hDerivative.
rewrite -hZero; exact:ExteriorDifferential.laws.
Qed.

(** Source for [exterior_derivative_squared_zero]: the
    fourth original displayed identity on p. 353,
    Federer 4.1.6, on every point of U.
    The chosen d phi agrees with its independently
    specified derivative graph, and its derivative is
    zero under literal twice differentiability on U. *)
Theorem exterior_derivative_squared_zero:
  (forall x,U x->exists z:Z 2%N,HD 2%N x z)->
  exists dphi:X->A_m X W m.+1,
    (forall x (L:Hom X (A_m X W m)),has_norm_differential NV P U phi x L->
      is_exterior_differential_value L (dphi x)) /\
    (forall x,U x->has_exterior_derivative NV Q U dphi x 0).
Proof.
move=>hTwice.
have [F hRep]:=@norm_higher_differential_representative_exists R X (A_m X W m)
  NV P hNV hNP Z evaluation ZN hZ U phi 1%N.
have hF x:U x->HD 1%N x (F x).
  move=>hx; have [z hz]:=hTwice x hx.
  have [w hw]:=norm_higher_differential_previous_domain hNV hz.
  by rewrite (hRep x w hw).
exists (fun x=>T (F x)); split.
- move=>x L hL.
  have hx:=norm_domain_interior_member hNV (norm_differential_interior hL).
  have hFirst:=(@norm_higher_differential_first R X (A_m X W m) NV P hNV hNP
    Z evaluation ZN hZ U phi x (F x)).1 (hF x hx).
  have hEqual:=norm_differential_unique hNV hNP hL hFirst.
  rewrite hEqual; exact:ExteriorDifferential.laws.
- move=>x hx; have [z hz]:=hTwice x hx.
  exact:(exterior_derivative_squared_at hF hz).
Qed.
End ExteriorDerivativeSquared.
