(** Federer (1969), 4.1.1, pp. 344–346: real
    evaluation sequences used in weak convergence and
    difference quotients. These supporting facts follow
    directly from the ordinary scalar norm topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormOpenTopology DirectedSeminormTopology
  OpenFamilyConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RealSequenceFacts.
Variable R:realType.
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).

(** Source for [real_open_scalar_ball]: translated real
    norm balls are open, supporting real evaluations
    in Federer 4.1.1, pp. 344–346. *)
Lemma real_open_scalar_ball (a e:R):RO [set t:R^o | `|t-a|<e].
Proof.
exact:(@seminorm_family_ball_open R R^o unit (fun (_:unit) (t:R^o)=>`|t|) RO
  (norm_single_seminorm_directed (@scalar_absolute_value_norm R))
  (norm_open_family_seminorm_laws (@scalar_absolute_value_norm R)) tt a e).
Qed.

(** Source for [real_open_convergent_sequence_bounded]: a
    convergent real sequence is bounded, supporting the
    common-support assertion for weak E' sequences
    in Federer 4.1.1, p. 344. *)
Theorem real_open_convergent_sequence_bounded (r:nat->R) b:
  open_family_converges RO (r @ \oo) b ->
  exists B:R,0<=B /\ forall n,`|r n|<=B.
Proof.
move=>hCvg.
have hb:([set t:R^o | `|t-b|<1]) b by rewrite /= subrr normr0 ltr01.
have [N _ hN]:=hCvg _ (@real_open_scalar_ball b 1) hb.
pose S:=\sum_(i<N) `|r i|.
have hS:0<=S by apply:sumr_ge0=>i _; exact:normr_ge0.
exists (S+`|b|+1); split; first by have:=normr_ge0 b; lra.
move=>n; case:(ltnP n N)=>hn.
- pose i:'I_N:=Ordinal hn.
  have hTerm:`|r n|<=S.
    rewrite /S (bigD1 i) //= lerDl; apply:sumr_ge0=>j _; exact:normr_ge0.
  have:=normr_ge0 b; lra.
- have hSmall:=hN n hn.
  change (is_true (`|r n-b|<1)) in hSmall.
  have hTriangle:=ler_normD (r n-b) b.
  rewrite subrK in hTriangle; lra.
Qed.

(** Source for [real_open_eventually_constant_limit]: the
    limit of an eventually constant real sequence is
    its constant value, supporting the weak sequence
    and derivative limits in Federer 4.1.1,
    pp. 344–346. *)
Theorem real_open_eventually_constant_limit (r:nat->R) a b:
  open_family_converges RO (r @ \oo) b ->
  (exists N,forall m,(N<=m)%N ->r m=a) ->a=b.
Proof.
move=>hCvg [N hConst]; case:(eqVneq a b)=>// hNe.
have hd:0<`|a-b| by rewrite normr_gt0 subr_eq0 hNe.
have hb:([set t:R^o | `|t-b|<`|a-b|]) b by rewrite /= subrr normr0.
have [M _ hM]:=hCvg _ (@real_open_scalar_ball b `|a-b|) hb.
have hBad:=hM (maxn M N) (leq_maxl M N).
change (is_true (`|r (maxn M N)-b|<`|a-b|)) in hBad.
by rewrite (hConst _ (leq_maxr M N)) ltxx in hBad.
Qed.
End RealSequenceFacts.
