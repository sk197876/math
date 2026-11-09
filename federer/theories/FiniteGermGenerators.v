(** Federer (1969), 3.4.5, p. 320: every
    finitely generated analytic-germ ideal has an actual finite
    analytic equation system on a common open neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormAnalyticUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRing AnalyticGermRingLaws CommutativeIdealUP FiniteAnalyticNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_germ_generator_system_exists]: the
    original finite analytic families used to define var(I),
    3.4.5, p. 320, exist for every finitely
    generated ideal. The chosen generators and functions
    remain local existence witnesses. *)
Theorem finite_germ_generator_system_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (I:set [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  is_finitely_generated_commutative_ideal I ->
  exists J:finType,exists f:J->@analytic_representative_type R X NX hNX a,
  exists U:set X,U a /\@open (real_norm_metric_space hNX) U /\
    (forall j,@norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
      U (analytic_representative_value (f j))) /\
    @is_generated_commutative_ideal [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]
      [set beta|exists j,analytic_germ (f j)=beta] I.
Proof.
move=>[F hF].
pose A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
pose J:=Finite.clone 'I_(size F) _.
pose z:A:=@analytic_germ_zero R X NX hNX a.
have hex j:exists p:@analytic_representative_type R X NX hNX a,analytic_germ p=nth z F j.
  exact:(@analytic_germ_has_representative R X NX hNX a (nth z F j)).
pose f (j:J):=projT1 (cid (hex j)).
have hf (j:J):analytic_germ (f j)=nth z F j:=projT2 (cid (hex j)).
have hFamily:[set beta:A|exists j:J,analytic_germ (f j)=beta]=[set beta:A|beta \in F].
  apply/seteqP;split.
  - move=>beta [j <-];rewrite hf;exact:mem_nth (ltn_ord j).
  - move=>beta hBeta.
    have hIndex:(index beta F<size F)%N by rewrite index_mem.
    exists (Ordinal hIndex);by rewrite hf /= nth_index.
have [U [ha [hU hAnalytic]]]:=@finite_analytic_representative_neighbourhood R X NX hNX a J f.
exists J,f,U;split;first exact:ha.
split;first exact:hU.
split;first exact:hAnalytic.
by rewrite hFamily.
Qed.
