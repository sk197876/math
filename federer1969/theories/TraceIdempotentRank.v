(** Federer (1969), 3.1.20, p. 233: an idempotent derivative
    has a discrete rank gap on the retract. This supporting route
    uses the trace of 1.4.5 instead of the printed exterior operator
    norm criterion; the open-and-closed maximal-rank argument is
    retained. The trace calculation is internal finite linear algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  LinearBasis FiniteCoordinates FiniteDualDimension Annihilator FiniteIndependence
  FiniteBasisComparison SimpleAdaptedBasis SubspaceStabiliser GrassmannAbbreviations
  LinearRankUP TraceDefinition Gamma GammaIntrinsic TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [trace_Hom_basis_independent]: the basis
    independence of the trace abbreviated in 1.4.5, p. 21,
    supporting the rank-gap argument in 3.1.20, p. 233. *)
Lemma trace_Hom_basis_independent (K:fieldType) (h2:(1+1:K)!=0)
    (X:lmodType K) (I J:finType) (b:I->X) (c:J->X)
    (hb:is_basis b) (hc:is_basis c) L :
  @trace_Hom K h2 X I b hb L=@trace_Hom K h2 X J c hc L.
Proof.
change (@trace K h2 X (@Gamma_include K h2 X X (@Gamma K X X I b hb L))=
  @trace K h2 X (@Gamma_include K h2 X X (@Gamma K X X J c hc L))).
by rewrite (Gamma_basis_independent hb hc).
Qed.

(** Source for [idempotent_trace_rank]: supporting closedness of
    the maximal derivative rank on B in Federer 3.1.20, p. 233.
    An idempotent fixes its range; in a basis extending a range
    basis its diagonal has r ones followed by zeros. Thus its
    trace is exactly the natural-number rank. *)
Theorem idempotent_trace_rank (K:fieldType) (h2:(1+1:K)!=0)
    (X:lmodType K) n (b:'I_n->X) (hb:is_basis b) (L:Hom X X) r :
  has_linear_rank L r -> hom_comp L L=L ->
  @trace_Hom K h2 X (Finite.clone 'I_n _) b hb L=r%:R.
Proof.
move=>[w hw] hLL.
pose W:=range_subspace (hom_as_linear L).
have hi:=@finite_independent_map K (Finite.clone 'I_r _) (subspace_space W) X
  (subspace_inclusion W) w (@subspace_val_injective K X W) (finite_basis_independent hw).
have hrn: (r<=n)%N.
  exact (@linear_rank_codomain_bound K X X L n b hb r (ex_intro _ w hw)).
have [l hn]:exists l,n=(r+l)%N by exists (n-r)%N; rewrite subnKC.
subst n.
have [c [hcb hew]]:=@finite_basis_extension_fixed K X r (r+l)
  (fun i=>subspace_val (w i)) b hrn hi hb.
have hcw i:c (lshift l i)=subspace_val (w i).
  have hi':lshift l i=widen_ord hrn i by apply: val_inj.
  by rewrite hi' hew.
have hLfix x:W x -> L x=x.
  move=>[v hv]; change (x=L v) in hv; rewrite hv.
  exact (congr1 (fun F:Hom X X=>F v) hLL).
have hleft i:dual_basis hcb (lshift l i) (L (c (lshift l i))) = 1.
  rewrite hLfix; last by rewrite hcw; exact: subspace_valP.
  by rewrite dual_basisE eqxx.
have hright j:dual_basis hcb (rshift r j) (L (c (rshift r j)))=0.
  have hmem:W (L (c (rshift r j))) by exists (c (rshift r j)).
  have hh:=@adapted_dual_right K X W r w hw l c hcb hcw (subspace_lift hmem) j.
  by rewrite subspace_liftE in hh.
have hsum1:(\sum_(i:'I_r) dual_basis hcb (lshift l i) (L (c (lshift l i))))=r%:R.
  have ->:(\sum_(i:'I_r) dual_basis hcb (lshift l i) (L (c (lshift l i))))=
      \sum_(i:'I_r) (1:K^o) by apply: eq_bigr=>i _; exact (hleft i).
  by rewrite sumr_const card_ord.
have hsum0:(\sum_(j:'I_l) dual_basis hcb (rshift r j) (L (c (rshift r j))))=0.
  apply: big1=>j _; exact (hright j).
by rewrite (trace_Hom_basis_independent h2 hb hcb) trace_HomE big_split_ord hsum1 hsum0 Monoid.mulm1.
Qed.
