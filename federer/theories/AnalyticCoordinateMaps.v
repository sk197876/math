(** Federer (1969), 3.1.24, p. 240: analyticity of the
    explicit source and target changes of coordinates of 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormDifferentialLinear
  NormRegularity NormAnalyticUP NormAnalyticLocal NormAnalyticLinear NormAnalyticOperations
  NormSourceChart NormSectionShearUP NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_source_chart_analytic]: g=(p f,q) in the
    analytic analogue of 3.1.18, stated in 3.1.24, p. 240.
    The source change is a sum of bounded linear maps and
    bounded linear composites of the given analytic map. *)
Theorem norm_source_chart_analytic (R:realType) (X Y V:lmodType R)
    (NX:X->R) (NY:Y->R) (NV:V->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (A:X->Prop) (beta:Hom X X) (i:Hom V X) (p:Hom Y V) (L:Hom X Y) (f:X->Y) :
  norm_bounded_linear NX NX beta -> norm_bounded_linear NV NX i ->
  norm_bounded_linear NY NV p -> norm_bounded_linear NX NY L ->
  @norm_analytic R X Y NX NY hNX hNY A f ->
  @norm_analytic R X X NX NX hNX hNX A (norm_source_chart beta i p L f).
Proof.
move=>hb hi hp hL hf.
have hclass:=norm_analytic_class_all_orders hf.
have hopen x (hx:A x):norm_domain_interior NX A x:=((hclass 0%N).1 x hx).1.
have hbc:=@norm_bounded_linear_analytic R X X NX NX hNX hNX A hopen beta hb.
have hpc:=@norm_bounded_linear_analytic R Y V NY NV hNY hNV (fun _=>True)
  (fun y _=>@norm_full_domain_interior R Y NY y) p hp.
have hpfc:=@norm_analytic_compose_on R X Y V NX NY NV hNX hNY hNV A (fun _=>True)
  f p (fun _ _=>Logic.I) hf hpc.
have hpLc:=@norm_bounded_linear_analytic R X V NX NV hNX hNV A hopen
  (hom_comp p L) (norm_bounded_linear_compose hL hp).
have hsub:=norm_analytic_subtract hpfc hpLc.
have hic:=@norm_bounded_linear_analytic R V X NV NX hNV hNX (fun _=>True)
  (fun v _=>@norm_full_domain_interior R V NV v) i hi.
have hisub:=@norm_analytic_compose_on R X V X NX NV NX hNX hNV hNX A (fun _=>True)
  (fun x=>p (f x)-p (L x)) i (fun _ _=>Logic.I) hsub hic.
exact (norm_analytic_add hbc hisub).
Qed.

(** Source for [norm_section_shears_analytic]: both explicit target
    shears of 3.1.18, p. 230, are analytic when the section is
    analytic, as asserted in 3.1.24, p. 240. Their precise
    inverse-image domain is retained. *)
Theorem norm_section_shears_analytic (R:realType) (Y V:lmodType R)
    (NY:Y->R) (NV:V->R) (hNY:is_real_norm NY) (hNV:is_real_norm NV)
    (p:Hom Y V) (j:Hom V Y) (B:V->Prop) (psi:V->Y) :
  norm_bounded_linear NY NV p -> norm_bounded_linear NV NY j ->
  @norm_analytic R V Y NV NY hNV hNY B psi ->
  @norm_analytic R Y Y NY NY hNY hNY (fun y=>B (p y)) (norm_section_shear p j psi) /\
  @norm_analytic R Y Y NY NY hNY hNY (fun y=>B (p y)) (norm_section_shear_inverse p j psi).
Proof.
move=>hp hj hpsi.
pose A:=fun y=>B (p y).
have hopen y (hy:A y):norm_domain_interior NY A y.
  have hpc:=@NormRegularityOperations.norm_class_linear R Y V NY NV hNY hNV (fun _=>True)
    p 0%N (fun v _=>@norm_full_domain_interior R Y NY v) hp.
  exact (@norm_class_zero_preimage_interior R Y V Y NY NV NY B p psi
    (hpc.1) ((norm_analytic_class_all_orders hpsi 0%N).1) y hy).
pose IY:=hom_of_linear (linear_id Y).
have hI:norm_bounded_linear NY NY IY.
  exists 1; split; first exact:ler01.
  by move=>y; rewrite hom_of_linearE mul1r.
have hIa:=@norm_bounded_linear_analytic R Y Y NY NY hNY hNY A hopen IY hI.
have hJPa:=@norm_bounded_linear_analytic R Y Y NY NY hNY hNY A hopen
  (hom_comp j p) (norm_bounded_linear_compose hp hj).
have hpa:=@norm_bounded_linear_analytic R Y V NY NV hNY hNV A hopen p hp.
have hpsia:=@norm_analytic_compose_on R Y V Y NY NV NY hNY hNV hNY A B p psi
  (fun y hy=>hy) hpa hpsi.
split.
- exact (norm_analytic_subtract (norm_analytic_add hIa hJPa) hpsia).
- exact (norm_analytic_add (norm_analytic_subtract hIa hJPa) hpsia).
Qed.
