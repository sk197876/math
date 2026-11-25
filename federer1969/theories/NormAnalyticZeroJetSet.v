(** Federer (1969), 3.1.24, p. 240: the set W
    where all actual differential fields vanish is open and
    closed relative to the domain of an analytic map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialSupport NormClassOneUP NormBoundedLinearTopology NormClassZeroTopology
  NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticFlatLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_zero_jet_set]: the set W in Federer
    3.1.24, p. 240, defined by vanishing of every
    supplied actual differential field, including order zero.
    The domain is explicit. No differential is chosen outside
    its actual graph. *)
Definition norm_zero_jet_set (R:realType) (X:lmodType R)
    (Z:nat->lmodType R) (A:set X) (D:forall i,X->Z i):set X :=
  fun x=>A x /\ forall i,D i x=0.

Section ZeroJets.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX NY hNX hNY).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX NY hNX hNY).
Variables (A:set X) (f:X->Y) (D:forall i,X->Z i).
Hypothesis hf:@norm_analytic R X Y NX NY hNX hNY A f.
Hypothesis hD:forall i x,A x -> has_norm_higher_differential NX ev ZN A f i x (D i x).
Hypothesis hDc:forall i,norm_class_zero NX (@ZN i) A (D i).
Local Notation W:=(norm_zero_jet_set A D).

(** Source for [norm_analytic_zero_jets_open]: W is open in
    Federer 3.1.24, p. 240. Taylor convergence gives a
    zero-function neighbourhood of each flat point; locality and
    uniqueness then make every differential vanish there. *)
Theorem norm_analytic_zero_jets_open : @open (real_norm_metric_space hNX) W.
Proof.
have hA x (hx:A x):norm_domain_interior NX A x:=((hDc 0%N) x hx).1.
rewrite openE=>a [ha hflat].
have hzero m (z:Z m) (hz:has_norm_higher_differential NX ev ZN A f m a z):z=0.
  rewrite (@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ A f
    m a z (D m a) hz (@hD m a ha)); exact (hflat m).
have [U [hUa [hUA [hOpen hUf]]]]:=@norm_analytic_flat_locally_zero R X Y NX NY hNX hNY A f a
  (@hf a ha) hzero.
have hUW x (hx:U x):W x.
  split; first exact (hUA x hx).
  move=>m.
  have hh:=@norm_higher_differential_locally_zero R X Y NX NY hNX hNY Z ev ZN hZ U f m x
    hOpen hUf hx.
  have hAz:=(@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
    m (fun _=>True) A f (fun x hx=>Logic.I) hA x (hUA x hx) 0).1 hh.
  exact (@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ A f
    m x (D m x) 0 (@hD m x (hUA x hx)) hAz).
have [r [hr hrU]]:=hOpen a hUa.
apply: (proj1 (@norm_domain_interior_neighbourhood R X NX hNX W a)).
exists r; split; first exact hr.
move=>v hv; exact (hUW (a+v) (hrU v hv)).
Qed.

(** Source for [norm_analytic_nonzero_jets_open]: the complement
    of W inside the open domain is open, supporting the
    relative closedness assertion in Federer 3.1.24, p. 240.
    One nonzero differential remains nonzero on a small ball,
    by continuity in its norm. *)
Theorem norm_analytic_nonzero_jets_open :
  @open (real_norm_metric_space hNX) (fun x=>A x /\ ~W x).
Proof.
rewrite openE=>a [ha hnW].
have [m hm]:exists m,D m a!=0.
  case:(pselect (exists m,D m a!=0))=>[h|h]; first exact h.
  exfalso; apply: hnW; split; first exact ha.
  move=>m; case:(pselect (D m a=0))=>[hm|hm]; first exact hm.
  exfalso; apply:h; exists m; by apply/eqP.
have hN:=continuous_multilinear_norm_is_norm hNY (hZ m).
have hp:0<ZN m (D m a) by rewrite (real_norm_positive hN.1 hN.2) hm.
have [r [hr hb]]:=@norm_class_zero_local_control R X (Z m) NX (@ZN m) hNX
  A (D m) a (ZN m (D m a)) (hDc m) ha hp.
apply: (proj1 (@norm_domain_interior_neighbourhood R X NX hNX (fun x=>A x /\ ~W x) a)).
exists r; split; first exact hr.
move=>v hv.
have hsmall:NX ((a+v)-a)<r by rewrite addrAC subrr add0r.
have [hav hrem]:=hb (a+v) hsmall.
split; first exact hav.
move=>[_ hz].
by rewrite (hz m) sub0r (real_seminorm_negate hN.1) ltxx in hrem.
Qed.

(** Source for [norm_analytic_zero_jets_relative_closed]: W is
    closed relative to the analytic domain A, Federer
    3.1.24, p. 240. Its relative complement is the
    open set where at least one actual differential is nonzero. *)
Theorem norm_analytic_zero_jets_relative_closed :
  exists2 C:set (real_norm_metric_space hNX),closed C & W=A `&` C.
Proof.
pose V:set (real_norm_metric_space hNX):=fun x=>A x /\ ~W x.
exists (~` V); first exact (open_closedC norm_analytic_nonzero_jets_open).
apply/seteqP; split=>x hx.
- split; first exact hx.1.
  by move=>[_ hn]; exact (hn hx).
- move:hx=>[ha hn]; apply: contrapT=>hW; apply:hn; by split.
Qed.
End ZeroJets.
