(** Federer (1969), 3.1.18, p. 230: differentiating p psi=identity
    and using image Dpsi subset image p* identifies Dpsi with p*. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialFiniteCalculus NormDifferentialLinear NormDifferentialLocal
  NormDifferentialDirectional GrassmannAbbreviations InnerProductUP
  LinearRangeProjection LinearRangeProjectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_section_derivative_right_inverse]: p Dpsi=id,
    the differentiated section equation in the last paragraph of
    Federer 3.1.18, p. 230. *)
Lemma norm_section_derivative_right_inverse (R:realType) (V Y:lmodType R)
    (NV:V->R) (NY:Y->R) (hNV:is_real_norm NV)
    (B:V->Prop) (psi:V->Y) (p:Hom Y V) a (J:Hom V Y) :
  norm_bounded_linear NY NV p -> (forall v, B v -> p (psi v)=v) ->
  has_norm_differential NV NY B psi a J -> forall v, p (J v)=v.
Proof.
move=>hp hsec hdpsi.
have hpost:=@norm_differential_postcompose R V Y V NV NY NV hNV B psi a J p hdpsi hp.
have hid:=norm_differential_domain_agreement hNV hsec hpost.
pose IV:=hom_of_linear (linear_id V).
have hI:norm_bounded_linear NV NV IV.
  exists 1; split; first exact: ler01.
  by move=>v; change (NV v<=1*NV v); rewrite mul1r.
have hlin:=@norm_differential_linear R V V NV NV hNV hNV B a IV
  (norm_differential_interior hdpsi) hI.
have heq:=norm_differential_unique hNV hNV hid hlin.
move=>v; exact (congr1 (fun L:Hom V V=>L v) heq).
Qed.

(** Source for [range_projection_section_unique]: image Dpsi subset
    image p* and p Dpsi=id force Dpsi=p*, the penultimate differential
    identity of Federer 3.1.18, p. 230. This is supporting linear algebra. *)
Lemma range_projection_section_unique (R:realType) (X Y:lmodType R)
    (C:Y->Y->R) (L:Hom X Y) v (p:{linear Y->R_n R v}) (j:{linear R_n R v->Y})
    (J:Hom (R_n R v) Y) :
  is_linear_range_projection C L p j ->
  (forall u, p (J u)=u) -> (forall u, exists x, L x=J u) ->
  J=hom_of_linear j.
Proof.
move=>hP hsec hIm; apply: hom_ext=>u.
have hh:=@range_projection_reconstruct R X Y C L v p j hP (J u) (hIm u).
by rewrite hsec in hh; exact: esym hh.
Qed.
