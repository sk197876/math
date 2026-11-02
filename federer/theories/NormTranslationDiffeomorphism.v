(** Federer (1969), 3.1.19, p. 231: translations of the local
    constant-rank source coordinates turn affine fibres into planes. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormRegularity
  NormRegularityOperations NormOpenDomainLaws NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_translation_diffeomorphism]: supporting
    translation of the source normal form for (2) implies (1),
    Federer 3.1.19, p. 231. A translation and its inverse have every
    class, on any normed space, including dimension zero. *)
Lemma norm_translation_diffeomorphism (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) c k :
  is_norm_diffeomorphism hNX hNX (fun _=>True) (fun _=>True)
    (fun x=>x-c) (fun y=>y+c) k.
Proof.
pose I:=hom_of_linear (linear_id X).
have hI:norm_bounded_linear NX NX I.
  exists 1; split; first exact: ler01.
  by move=>x; change (NX x<=1*NX x); rewrite mul1r.
have hopen x (_:True):norm_domain_interior NX (fun _=>True) x:=norm_full_domain_interior NX x.
have hcI:=@norm_class_linear R X X NX NX hNX hNX (fun _=>True) I k hopen hI.
have hcC:=@norm_class_constant R X X NX NX hNX hNX (fun _=>True) c k hopen.
have hf:=norm_class_subtract hcI hcC.
have hg:=norm_class_add hcI hcC.
constructor=>//.
- exists I,I; split=>//; split=>//; split; by move=>x.
- by move=>x _; rewrite subrK.
- by move=>y _; rewrite addrK.
Qed.
