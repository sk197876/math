(** Federer (1969), 3.1.18, p. 230: the target diffeomorphism
    h=identity+p*p-psi p and its displayed inverse. The proof uses
    only the abstract linear right-inverse and section laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormClassOneUP
  NormDifferentialLinear NormClassZeroComposition NormRegularity
  NormRegularityOperations NormOpenDomainLaws NormDiffeomorphismUP.
From Federer Require Export NormSectionShearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Shear.
Variable R:realType.
Variables Y V:lmodType R.
Variables (NY:Y->R) (NV:V->R).
Hypothesis hNY:is_real_norm NY.
Hypothesis hNV:is_real_norm NV.
Variable p:Hom Y V.
Variable j:Hom V Y.
Hypothesis hp:norm_bounded_linear NY NV p.
Hypothesis hj:norm_bounded_linear NV NY j.
Hypothesis hpj:cancel j p.
Variable B:V->Prop.
Variable psi:V->Y.
Variable k:nat.
Hypothesis hpsi:norm_class hNV hNY B psi k.
Hypothesis hsection:forall v, B v -> p (psi v)=v.
Local Notation A := (fun y=>B (p y)).
Local Notation norm_section_shear := (@NormSectionShearUP.norm_section_shear R Y V p j psi).
Local Notation norm_section_shear_inverse := (@NormSectionShearUP.norm_section_shear_inverse R Y V p j psi).

(** Source for [norm_section_shear_projection]: p h=p, as stated
    in Federer 3.1.18, p. 230. *)
Lemma norm_section_shear_projection y : A y -> p (norm_section_shear y)=p y.
Proof. move=>hy; by rewrite /norm_section_shear linearB linearD /= hpj hsection // addrK. Qed.

(** Source for [norm_section_shear_inverse_projection]: supporting
    p h inverse=p, preserving the inverse-image domain in 3.1.18, p. 230. *)
Lemma norm_section_shear_inverse_projection y : A y -> p (norm_section_shear_inverse y)=p y.
Proof. move=>hy; by rewrite /norm_section_shear_inverse linearD linearB /= hpj hsection // subrr add0r. Qed.

(** Source for [norm_section_shear_cancel]: the first inverse identity
    for the target change in Federer 3.1.18, p. 230. *)
Lemma norm_section_shear_cancel y : A y ->
  norm_section_shear_inverse (norm_section_shear y)=y.
Proof.
move=>hy; rewrite /norm_section_shear_inverse norm_section_shear_projection //.
by rewrite /norm_section_shear addrAC subrK addrK.
Qed.

(** Source for [norm_section_shear_inverse_cancel]: the second inverse
    identity for the target change in Federer 3.1.18, p. 230. *)
Lemma norm_section_shear_inverse_cancel y : A y ->
  norm_section_shear (norm_section_shear_inverse y)=y.
Proof.
move=>hy; rewrite /norm_section_shear norm_section_shear_inverse_projection //.
by rewrite /norm_section_shear_inverse addrAC addrK subrK.
Qed.

(** Source for [norm_section_shear_domain_open]: p inverse(V) is open,
    supporting the actual domain of the diffeomorphism in 3.1.18, p. 230. *)
Lemma norm_section_shear_domain_open y : A y -> norm_domain_interior NY A y.
Proof.
have hpclass := @norm_class_linear R Y V NY NV hNY hNV (fun _=>True) p k
  (fun x _=>@norm_full_domain_interior R Y NY x) hp.
exact (@norm_class_zero_preimage_interior R Y V Y NY NV NY B p psi
  (norm_class_continuous hpclass) (norm_class_continuous hpsi) y).
Qed.

(** Source for [norm_section_shear_class]: the target change h has
    class k, Federer 3.1.18, p. 230, by 3.1.11's class calculus. *)
Lemma norm_section_shear_class : norm_class hNY hNY A norm_section_shear k.
Proof.
pose IY := hom_of_linear (linear_id Y).
have hI:norm_bounded_linear NY NY IY.
  exists 1; split; first exact: ler01.
  by move=>y; change (NY y<=1*NY y); rewrite mul1r.
have hopen := norm_section_shear_domain_open.
have hIc := @norm_class_linear R Y Y NY NY hNY hNY A IY k hopen hI.
have hJP := norm_bounded_linear_compose hp hj.
have hJPc := @norm_class_linear R Y Y NY NY hNY hNY A (hom_comp j p) k hopen hJP.
have hpc := @norm_class_linear R Y V NY NV hNY hNV A p k hopen hp.
have hpsic := @norm_class_compose_on R Y V Y NY NV NY hNY hNV hNY
  A B p psi k (fun x (hx:A x)=>hx) hpc hpsi.
exact (norm_class_subtract (norm_class_add hIc hJPc) hpsic).
Qed.

(** Source for [norm_section_shear_inverse_class]: the displayed inverse
    has class k, Federer 3.1.18, p. 230. *)
Lemma norm_section_shear_inverse_class :
  norm_class hNY hNY A norm_section_shear_inverse k.
Proof.
pose IY := hom_of_linear (linear_id Y).
have hI:norm_bounded_linear NY NY IY.
  exists 1; split; first exact: ler01.
  by move=>y; change (NY y<=1*NY y); rewrite mul1r.
have hopen := norm_section_shear_domain_open.
have hIc := @norm_class_linear R Y Y NY NY hNY hNY A IY k hopen hI.
have hJP := norm_bounded_linear_compose hp hj.
have hJPc := @norm_class_linear R Y Y NY NY hNY hNY A (hom_comp j p) k hopen hJP.
have hpc := @norm_class_linear R Y V NY NV hNY hNV A p k hopen hp.
have hpsic := @norm_class_compose_on R Y V Y NY NV NY hNY hNV hNY
  A B p psi k (fun x (hx:A x)=>hx) hpc hpsi.
exact (norm_class_add (norm_class_subtract hIc hJPc) hpsic).
Qed.

(** Source for [norm_section_shear_diffeomorphism]: the target change
    on p inverse(V) is a diffeomorphism of class k, Federer 3.1.18,
    p. 230. Both maps, actual domains, and cancellation laws are proved. *)
Theorem norm_section_shear_diffeomorphism :
  is_norm_diffeomorphism hNY hNY A A norm_section_shear norm_section_shear_inverse k.
Proof.
constructor.
- pose IY := hom_of_linear (linear_id Y).
  have hI:norm_bounded_linear NY NY IY.
    exists 1; split; first exact: ler01.
    by move=>y; change (NY y<=1*NY y); rewrite mul1r.
  exists IY, IY; split=>//; split=>//; split; by move=>y.
- exact: norm_section_shear_class.
- exact: norm_section_shear_inverse_class.
- by move=>y hy; rewrite /A norm_section_shear_projection.
- by move=>y hy; rewrite /A norm_section_shear_inverse_projection.
- exact: norm_section_shear_cancel.
- exact: norm_section_shear_inverse_cancel.
Qed.
End Shear.
