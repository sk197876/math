(** Federer (1969), 3.1.18, p. 230, final display: Dh[f(a)]=identity
    once Dpsi[(p f)(a)]=p*. The proof keeps the actual inverse-image
    domain and uses only the abstract section laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialChain NormDifferentialLocal
  NormDifferentialArithmetic NormDifferentialSubtraction NormClassOneUP
  NormRegularity NormSectionShear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_section_shear_differential_identity]: the final
    differential normalization in Federer 3.1.18, p. 230. The graph
    statement identifies the actual first differential without selecting
    an artificial value outside the domain. *)
Theorem norm_section_shear_differential_identity (R:realType) (Y V:lmodType R)
    (NY:Y->R) (NV:V->R) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (p:Hom Y V) (j:Hom V Y) (B:V->Prop) (psi:V->Y) y k :
  norm_bounded_linear NY NV p -> norm_bounded_linear NV NY j ->
  cancel j p -> norm_class hNV hNY B psi k ->
  (forall v, B v -> p (psi v)=v) -> B (p y) ->
  has_norm_differential NV NY B psi (p y) j ->
  has_norm_differential NY NY (fun z=>B (p z))
    (@norm_section_shear R Y V p j psi) y (hom_of_linear (linear_id Y)).
Proof.
move=>hp hj hpj hpsi hsec hy hdpsi.
pose A:=fun z=>B (p z).
have hopen:=@norm_section_shear_domain_open R Y V NY NV hNY hNV p hp B psi k hpsi y hy.
pose IY:=hom_of_linear (linear_id Y).
have hI:norm_bounded_linear NY NY IY.
  exists 1; split; first exact: ler01.
  by move=>z; change (NY z<=1*NY z); rewrite mul1r.
have hdI:=@norm_differential_linear R Y Y NY NY hNY hNY A y IY hopen hI.
have hjp:=@norm_bounded_linear_compose R Y V Y NY NV NY p j hp hj.
have hdjp:=@norm_differential_linear R Y Y NY NY hNY hNY A y (hom_comp j p) hopen hjp.
have hdp:=@norm_differential_linear R Y V NY NV hNY hNV A y p hopen hp.
have hchain:=norm_differential_chain hNY hNV hNY hdp hdpsi.
have hdpsip:=@norm_differential_restrict R Y Y NY NY (fun z=>A z /\ B (p z)) A
  (fun z=>psi (p z)) y (hom_comp j p) (fun z hz=>conj hz hz) hopen hchain.
have hh:=norm_differential_subtract hNY hNY (norm_differential_add hNY hdI hdjp) hdpsip.
by rewrite addrK in hh.
Qed.
