(** Federer (1969), 3.1.18, p. 229: a source change whose first
    coordinates are p f and whose differential at a is invertible.
    We express the printed product coordinates inside an isomorphic
    copy of the source space, using a linear chart beta with first
    coordinates p Df(a). This is the same complementary-coordinate
    construction, without exposing the chosen linear chart. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialSubtraction
  NormDifferentialChain NormDifferentialLocal NormClassOneUP NormRegularity
  NormRegularityOperations NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_linear_postcompose]: supporting
    D(p f)=p Df, used repeatedly in Federer 3.1.18, pp. 229–230.
    The restriction keeps exactly the original domain of f. *)
Lemma norm_differential_linear_postcompose (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (f:X->Y) a (L:Hom X Y) (p:Hom Y Z) :
  has_norm_differential NX NY A f a L -> norm_bounded_linear NY NZ p ->
  has_norm_differential NX NZ A (fun x=>p (f x)) a (hom_comp p L).
Proof.
move=>hf hp.
have hlin:=@norm_differential_linear R Y Z NY NZ hNY hNZ setT (f a) p
  (@norm_full_domain_interior R Y NY (f a)) hp.
have hcomp:=norm_differential_chain hNX hNY hNZ hf hlin.
exact (@norm_differential_restrict R X Z NX NZ (fun x=>A x /\ True) A
  (fun x=>p (f x)) a (hom_comp p L) (fun x hx=>conj hx I)
  (norm_differential_interior hf) hcomp).
Qed.

(** Source for [norm_source_chart]: supporting expression of the source
    chart g=(p f,q) in Federer 3.1.18, p. 229. The fixed linear chart
    beta carries the p L coordinates; adding i(p f-p L) replaces
    precisely those first coordinates. *)
Definition norm_source_chart (R:realType) (X Y V:lmodType R)
    (beta:Hom X X) (i:Hom V X) (p:Hom Y V) (L:Hom X Y) (f:X->Y) x :=
  beta x+i (p (f x)-p (L x)).

(** Source for [norm_source_chart_prefix]: p f=r g in Federer 3.1.18,
    p. 230, follows from the first-coordinate laws of the source chart. *)
Lemma norm_source_chart_prefix (R:realType) (X Y V:lmodType R)
    (beta:Hom X X) (i:Hom V X) (p:Hom Y V) (L:Hom X Y)
    (r:Hom X V) (f:X->Y) :
  cancel i r -> (forall x, r (beta x)=p (L x)) ->
  forall x, r (norm_source_chart beta i p L f x)=p (f x).
Proof.
move=>hir hb x; rewrite /norm_source_chart linearD /= hir hb.
by rewrite addrC subrK.
Qed.

(** Source for [norm_source_chart_class]: the source coordinate change
    has the same class as f, supporting Federer 3.1.18, p. 229.
    Only the public class calculus and finite bounds are used. *)
Theorem norm_source_chart_class (R:realType) (X Y V:lmodType R)
    (NX:X->R) (NY:Y->R) (NV:V->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (A:X->Prop) (beta:Hom X X) (i:Hom V X) (p:Hom Y V) (L:Hom X Y)
    (f:X->Y) k :
  norm_bounded_linear NX NX beta -> norm_bounded_linear NV NX i ->
  norm_bounded_linear NY NV p -> norm_bounded_linear NX NY L ->
  norm_class hNX hNY A f k ->
  norm_class hNX hNX A (norm_source_chart beta i p L f) k.
Proof.
move=>hb hi hp hL hf.
have hopen x (hx:A x) := (@norm_class_continuous R X Y NX NY hNX hNY A f k hf x hx).1.
have hbc:=@norm_class_linear R X X NX NX hNX hNX A beta k hopen hb.
have hpc:=@norm_class_linear R Y V NY NV hNY hNV setT p k
  (fun y _=>@norm_full_domain_interior R Y NY y) hp.
have hpfc:=@norm_class_compose_on R X Y V NX NY NV hNX hNY hNV A setT f p k
  (fun x _=>I) hf hpc.
have hpL:=norm_bounded_linear_compose hL hp.
have hpLc:=@norm_class_linear R X V NX NV hNX hNV A (hom_comp p L) k hopen hpL.
have hsub:=norm_class_subtract hpfc hpLc.
have hic:=@norm_class_linear R V X NV NX hNV hNX setT i k
  (fun v _=>@norm_full_domain_interior R V NV v) hi.
have hisub:=@norm_class_compose_on R X V X NX NV NX hNX hNV hNX A setT
  (fun x=>p (f x)-p (L x)) i k (fun x _=>I) hsub hic.
exact (norm_class_add hbc hisub).
Qed.

(** Source for [norm_source_chart_differential]: the differential of
    the source chart at a is the linear isomorphism beta. This supports
    the injectivity inference for Dg(a) in Federer 3.1.18, p. 229. *)
Theorem norm_source_chart_differential (R:realType) (X Y V:lmodType R)
    (NX:X->R) (NY:Y->R) (NV:V->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (A:X->Prop) (beta:Hom X X) (i:Hom V X) (p:Hom Y V) (L:Hom X Y)
    (f:X->Y) a :
  norm_bounded_linear NX NX beta -> norm_bounded_linear NV NX i ->
  norm_bounded_linear NY NV p -> has_norm_differential NX NY A f a L ->
  has_norm_differential NX NX A (norm_source_chart beta i p L f) a beta.
Proof.
move=>hb hi hp hf.
have hopen:=norm_differential_interior hf.
have hbc:=@norm_differential_linear R X X NX NX hNX hNX A a beta hopen hb.
have hpfc:=@norm_differential_linear_postcompose R X Y V NX NY NV hNX hNY hNV
  A f a L p hf hp.
have hpL:=norm_bounded_linear_compose (norm_differential_bounded hf) hp.
have hpLc:=@norm_differential_linear R X V NX NV hNX hNV A a (hom_comp p L) hopen hpL.
have hsub:=norm_differential_subtract hNX hNV hpfc hpLc.
rewrite subrr in hsub.
have hisub:=@norm_differential_linear_postcompose R X V X NX NV NX hNX hNV hNX
  A (fun x=>p (f x)-p (L x)) a 0 i hsub hi.
have hz:hom_comp i (0:Hom X V)=0.
  apply: hom_ext=>x; by rewrite hom_compE hom_zeroE linear0.
rewrite hz in hisub.
have hh:=norm_differential_add hNX hbc hisub.
by rewrite addr0 in hh.
Qed.
