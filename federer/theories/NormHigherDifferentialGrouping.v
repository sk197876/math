(** Federer (1969), 3.1.11, p. 219:
    the exact D^q D^p identity, expressed
    through abstract isometric grouping maps.
    The domain of D^p f is its exact
    partial domain, including at higher orders. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormDifferentialLocalAgreement ContinuousMultilinearUP
  NormHigherDifferentialUP MultilinearArguments MultilinearSuccessorArguments
  MultilinearDegreeTransport MultilinearGroupingCompatibility NormLinearIsometryInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Grouping.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Variable Z : nat->lmodType R.
Variable ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i).
Variable p : nat.
Variable W : nat->lmodType R.
Variable ew : forall q, {ffun 'I_q->X}->Hom (W q) (Z p).
Variable WN : forall q, W q->R.
Variable J : forall q, Hom (Z (p+q)%N) (W q).
Variable K : forall q, Hom (W q) (Z (p+q)%N).
Hypothesis hJ : forall q z u v,
  @ez p u (@ew q v (J q z))=@ez (p+q)%N (multilinear_arguments_join u v) z.
Hypothesis hJN : forall q z, @WN q (J q z)=@ZN (p+q)%N z.
Hypothesis hJK : forall q w, J q (K q w)=w.
Hypothesis hKJ : forall q z, K q (J q z)=z.
Variable A : X->Prop.
Variable f : X->Y.
Variable G : X->Z p.
Hypothesis hG : forall x z, has_norm_higher_differential NX ez ZN A f p x z -> G x=z.
Local Notation HDZ := (@has_norm_higher_differential R X Y NX Z ez ZN A f).
Local Notation B := (fun x=>exists z, HDZ p x z).
Local Notation HDW := (@has_norm_higher_differential R X (Z p) NX W ew WN B G).

(** Source for [norm_higher_differential_grouping]:
    Federer 3.1.11, p. 219, the
    displayed D^(p+q) f and D^q D^p f
    relation. The grouping maps obey their proved
    evaluation and isometry laws; the theorem does
    not replace the exact D^p domain by an
    assumed open subset or impose class regularity. *)
Theorem norm_higher_differential_grouping q a (w : W q) :
  HDW q a w <-> exists z : Z (p+q)%N, HDZ (p+q)%N a z /\ w=J q z.
Proof.
have hKN j v : @ZN (p+j)%N (K j v)=@WN j v.
  by rewrite -hJN hJK.
have hKb j : norm_bounded_linear (@WN j) (@ZN (p+j)%N) (K j).
  exact (@norm_linear_isometry_bounded R (W j) (Z (p+j)%N)
    (@WN j) (@ZN (p+j)%N) (K j) (hKN j)).
have hJb j : norm_bounded_linear (@ZN (p+j)%N) (@WN j) (J j).
  exact (@norm_linear_isometry_bounded R (Z (p+j)%N) (W j)
    (@ZN (p+j)%N) (@WN j) (J j) (@hJN j)).
elim: q a w=>[|q ih] a w.
- split.
  + move=> [ha hw].
    pose z := K 0%N w.
    have hz : J 0%N z=w := @hJK 0%N w.
    have hc := @multilinear_grouping_zero R p X Y (W 0%N) Z NX NY
      ez ZN (@hZ p) (@ew 0%N) (J 0%N) (@hJ 0%N) z
      [ffun i : 'I_0=>(0:X)].
    rewrite hz in hc.
    have [v hv] := ha.
    have hcast : multilinear_degree_cast Z (addn0 p) z=v.
      by rewrite -hc hw (@hG a v hv).
    exists z; split; last exact: esym hz.
    apply: (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
      A f (p+0)%N p (addn0 p) a z).2.
    by rewrite hcast.
  + move=> [z [hz ->]]; split.
    * exists (multilinear_degree_cast Z (addn0 p) z).
      exact: (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
        A f (p+0)%N p (addn0 p) a z).1 hz.
    * rewrite (@multilinear_grouping_zero R p X Y (W 0%N) Z NX NY
        ez ZN (@hZ p) (@ew 0%N) (J 0%N) (@hJ 0%N)).
      symmetry; apply: hG.
      exact: (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
        A f (p+0)%N p (addn0 p) a z).1 hz.
- have hdom x : (exists v, HDW q x v)<->(exists z, HDZ (p+q)%N x z).
    split.
    + move=> [v hv]; have [z [hz _]] := (ih x v).1 hv; by exists z.
    + move=> [z hz]; exists (J q z); apply: (ih x (J q z)).2; by exists z.
  split.
  + move=> [g [hg [L [hL he]]]].
    pose z := K q.+1 w.
    have hzw : J q.+1 z=w := @hJK q.+1 w.
    pose gZ x := K q (g x).
    pose LZ := hom_comp (K q) L.
    have hgZ x u : HDZ (p+q)%N x u -> gZ x=u.
      move=> hu.
      have hv : HDW q x (J q u) by apply: (ih x (J q u)).2; by exists u.
      by rewrite /gZ (hg x (J q u) hv) hKJ.
    have hpost := norm_differential_postcompose hNX hL (hKb q).
    have hDZ : has_norm_differential NX (@ZN (p+q)%N)
        (fun x=>exists u, HDZ (p+q)%N x u) gZ a LZ.
      apply: (@norm_differential_local_agreement R X (Z (p+q)%N)
        NX (@ZN (p+q)%N) hNX (fun x=>exists v, HDW q x v)
        (fun x=>exists u, HDZ (p+q)%N x u) gZ gZ a LZ
        1 ltr01 _ _ hpost).
      - move=> h _; exact: hdom.
      - by move=> h _ _.
    have heZ : forall u x, @ez (p+q)%N u (LZ x)=
        @ez (p+q).+1 (multilinear_successor_arguments u x)
          (multilinear_degree_cast Z (addnS p q) z).
      apply: (@multilinear_grouping_successor_iff R p q X Y (Z p)
        (W q) (W q.+1) Z NX NY (@ez p) (@ZN p) (@hZ p)
        ez (@ew q) (@ew q.+1) (J q) (J q.+1) (@hJ q) (@hJ q.+1) LZ z).2.
      move=> v x; by rewrite hom_compE /LZ hom_compE hJK hzw; exact: he.
    exists z; split; last exact: esym hzw.
    apply: (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
      A f (p+q.+1)%N (p+q).+1 (addnS p q) a z).2.
    by exists gZ; split=> //; exists LZ.
  + move=> [z [hz ->]].
    have hs := (@norm_higher_differential_degree_cast R X Y NX Z ez ZN
      A f (p+q.+1)%N (p+q).+1 (addnS p q) a z).1 hz.
    have [g [hg [L [hL he]]]] := hs.
    pose gW x := J q (g x).
    pose LW := hom_comp (J q) L.
    have hgW x v : HDW q x v -> gW x=v.
      move=> hv; have [u [hu ->]] := (ih x v).1 hv.
      by rewrite /gW (hg x u hu).
    have hpost := norm_differential_postcompose hNX hL (hJb q).
    have hDW : has_norm_differential NX (@WN q)
        (fun x=>exists v, HDW q x v) gW a LW.
      apply: (@norm_differential_local_agreement R X (W q)
        NX (@WN q) hNX (fun x=>exists u, HDZ (p+q)%N x u)
        (fun x=>exists v, HDW q x v) gW gW a LW 1 ltr01 _ _ hpost).
      - move=> h _; exact: iff_sym (hdom (a+h)).
      - by move=> h _ _.
    exists gW; split; first exact hgW.
    exists LW; split; first exact hDW.
    exact: (@multilinear_grouping_successor_iff R p q X Y (Z p)
      (W q) (W q.+1) Z NX NY (@ez p) (@ZN p) (@hZ p)
      ez (@ew q) (@ew q.+1) (J q) (J q.+1) (@hJ q) (@hJ q.+1) L z).1 he.
Qed.
End Grouping.
