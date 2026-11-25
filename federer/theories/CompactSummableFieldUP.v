(** Federer (1969), 4.1.18, p. 375: Omega_m consists of
    summable multivector fields with compact support in U.
    The following supporting specification allows any normed
    coefficient space. It uses genuine total-domain functions,
    as required for the vector-space assertion by the May 1987
    erratum, p. 1, book p. 86 bottom. No quotient by almost
    equality, and hence no positive-definiteness claim, is made. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient
  SubspaceCarrier PartialFunctionBasic MeasureUP MeasurableNormedFunctionUP
  TotalMeasurableFunctionSpace MeasureLpNormTotal ExtendedSeminormUP
  ExtendedSeminormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section CompactSummableFields.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation A:=(@total_measurable_normed_subspace R X V N hN mu hm).
Local Notation AT:=(subspace_space A).
Local Notation L:=(@total_measurable_lp_norm R X V N hN mu hm 1).

(** Source for [compact_summable_field_member]: the independent
    compact support and finite L1 requirements for Omega_m in
    Federer 4.1.18, p. 375. On the actual open-domain subtype,
    compactness is compactness inside the original U. *)
Definition compact_summable_field_member (f:AT):Prop:=
  L f< +oo /\ exists K:set X,compact K /\
    forall x,~K x->subspace_val f x=0%R.

(** Source for [compact_summable_field_subspace]: the vector-space
    assertion implicit in Omega_m and the linear q of Federer
    4.1.18, p. 375. Finiteness uses the earlier L1 seminorm;
    compact supports are combined by their finite union. *)
Definition compact_summable_field_subspace:subspace AT.
Proof.
pose hL:=@total_measurable_lp_norm_seminorm R X V N hN mu hm 1 (lexx 1).
refine (@Subspace R AT compact_summable_field_member _ _ _).
- split.
  + by rewrite (extended_seminorm_zero hL) ltry.
  + exists set0;split;first exact:compact0.
    move=>x _;by rewrite linear0.
- move=>f g [hF [K [hK hFK]]] [hG [J [hJ hGJ]]];split.
  + exact:(@extended_seminorm_finite_add R AT L hL f g hF hG).
  + exists (K `|` J);split;first exact:(compactU hK hJ).
    move=>x hx.
    have hxK:~K x by move=>h;apply:hx;left.
    have hxJ:~J x by move=>h;apply:hx;right.
    rewrite linearD.
    change ((subspace_val f x+subspace_val g x)%R=0%R).
    by rewrite (hFK x hxK) (hGJ x hxJ) add0r.
- move=>c f [hF [K [hK hFK]]];split.
  + exact:(@extended_seminorm_finite_scale R AT L hL c f hF).
  + exists K;split=>//x hx.
    rewrite linearZ.
    change ((c*:subspace_val f x)%R=0%R).
    by rewrite (hFK x hx) scaler0.
Defined.
End CompactSummableFields.
