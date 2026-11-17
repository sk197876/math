(** Federer (1969), 3.4.11, p. 338:
    select finitely many original leading polynomials that
    generate the actual leading ideal. Reuse the proved
    Noetherian original-generator theorem and retain every source
    germ, exact degree, polynomial and representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives
  CommutativeIdealUP CommutativeIdealExistence CommutativeIdealSealed AnalyticInitialPolynomialUP
  AnalyticInitialPolynomialGermUP AnalyticInitialIdealSealed NoetherianOriginalGenerators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_initial_finite_family_exists]: the
    finite original homogeneous polynomial family in 3.4.11,
    p. 338. Its members are original initial
    polynomials, rather than arbitrary analytic combinations of
    them. The finite family may be empty. *)
Theorem analytic_initial_finite_family_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (I:set (@analytic_germ_ring R X NX hNX 0)):
  is_noetherian_commutative_ring [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] ->
  exists J:finType,exists a:J->@analytic_germ_ring R X NX hNX 0,
  exists k:J->nat,exists P:J->X->R,exists f:J->@analytic_representative_type R X NX hNX 0,
    (forall j,I (a j) /\is_initial_analytic_germ_polynomial (a j) (k j) (P j) /\
      forall x,analytic_representative_value (f j) x= P j x) /\
    @is_generated_commutative_ideal [the comNzRingType of (@analytic_germ_ring R X NX hNX 0)]
      [set beta|exists j,analytic_germ (f j)=beta]
      (@AnalyticInitialIdeal.value R X NX hNX I).
Proof.
move=>hNoetherian.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose F:=@analytic_initial_polynomial_generators R X NX hNX I.
have [L [hOriginal hGenerated]]:=@noetherian_finite_original_generators G F hNoetherian.
pose J:=Finite.clone 'I_(size L) _.
have hEach (j:J):exists a:G,I a /\is_initial_polynomial_germ a (nth 0 L j).
  exact:hOriginal _ (mem_nth 0 (ltn_ord j)).
have [a hA]:=choice hEach.
have hDegree j:exists k (P:X->R) (f:@analytic_representative_type R X NX hNX 0),
    is_initial_analytic_germ_polynomial (a j) k P /\
    (forall x,analytic_representative_value f x= P x) /\analytic_germ f=nth 0 L j.
  exact:(hA j).2.
have [k hK]:=choice hDegree.
have [P hP]:=choice hK.
have [f hF]:=choice hP.
exists J,a,k,P,f;split.
- move=>j;split;first exact:(hA j).1.
  split;first exact:(hF j).1.
  exact:(hF j).2.1.
- have hFamily:[set beta:G|exists j:J,analytic_germ (f j)=beta]=[set beta:G|beta \in L].
    apply/seteqP;split.
    + move=>beta [j <-];rewrite (hF j).2.2;exact:mem_nth (ltn_ord j).
    + move=>beta hBeta.
      have hIndex:(index beta L<size L)%N by rewrite index_mem.
      exists (Ordinal hIndex);by rewrite (hF _).2.2 /= nth_index.
  rewrite hFamily.
  have hLeast:=@AnalyticInitialIdeal.laws R X NX hNX I.
  have hEqual:@AnalyticInitialIdeal.value R X NX hNX I=@GeneratedCommutativeIdeal.value G F.
    exact:(@generated_commutative_ideal_unique G F
      (@AnalyticInitialIdeal.value R X NX hNX I) (@GeneratedCommutativeIdeal.value G F)
      hLeast (@GeneratedCommutativeIdeal.laws G F)).
  rewrite hEqual hGenerated;exact:GeneratedCommutativeIdeal.laws.
Qed.
