(** Federer (1969), 3.1.18, p. 229: diffeomorphisms of class k between
    open subsets of isomorphic normed spaces. State the ambient linear
    isomorphism, class and inverse laws abstractly; homeomorphism of the
    actual subspaces is a consequence of those laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormMetric
  NormClassOneUP NormClassZeroTopology NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_spaces_isomorphic]: the isomorphic ambient normed
    spaces in the definition of diffeomorphism, Federer 3.1.18, p. 229.
    A continuous linear isomorphism and its continuous inverse are
    specified by finite norm bounds and cancellation laws. *)
Definition norm_spaces_isomorphic (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) :=
  exists (L : Hom X Y) (M : Hom Y X),
    norm_bounded_linear NX NY L /\ norm_bounded_linear NY NX M /\
    cancel L M /\ cancel M L.

(** Source for [norm_spaces_isomorphic_symmetric]: supporting symmetry
    of the ambient isomorphism in Federer 3.1.18, p. 229. *)
Lemma norm_spaces_isomorphic_symmetric (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) :
  norm_spaces_isomorphic NX NY -> norm_spaces_isomorphic NY NX.
Proof.
move=>[L [M [hL [hM [hLM hML]]]]].
exists M, L; split=>//; split=>//; by split.
Qed.

(** Source for [is_norm_diffeomorphism]: the definition in Federer
    3.1.18, p. 229: a homeomorphism of class k whose inverse has class k,
    with domain and image open in isomorphic normed spaces. Openness and
    continuity follow from the class predicates and are proved separately;
    the maps' total representatives outside their domains are irrelevant. *)
Record is_norm_diffeomorphism (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (B : set Y) (f : X->Y) (g : Y->X) (k : nat) : Prop := {
  (** Source for [norm_diffeomorphism_spaces]: the ambient isomorphism
      convention in Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_spaces : norm_spaces_isomorphic NX NY;
  (** Source for [norm_diffeomorphism_forward_class]: f has class k on
      its actual domain, Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_forward_class : norm_class hNX hNY A f k;
  (** Source for [norm_diffeomorphism_inverse_class]: the inverse has
      class k on the actual image, Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_inverse_class : norm_class hNY hNX B g k;
  (** Source for [norm_diffeomorphism_maps]: f maps its domain into its
      image, supporting the definition in Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_maps : forall x, A x -> B (f x);
  (** Source for [norm_diffeomorphism_inverse_maps]: the inverse maps
      the image into the domain, Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_inverse_maps : forall y, B y -> A (g y);
  (** Source for [norm_diffeomorphism_left_inverse]: inverse identity
      on the actual domain, Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_left_inverse : forall x, A x -> g (f x)=x;
  (** Source for [norm_diffeomorphism_right_inverse]: inverse identity
      on the actual image, Federer 3.1.18, p. 229. *)
  norm_diffeomorphism_right_inverse : forall y, B y -> f (g y)=y
}.

(** Source for [norm_diffeomorphism_symmetric]: supporting the inverse
    of a diffeomorphism in Federer 3.1.18, p. 229. *)
Lemma norm_diffeomorphism_symmetric (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (B : set Y) (f : X->Y) (g : Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  is_norm_diffeomorphism hNY hNX B A g f k.
Proof.
move=>[hS hf hg hfB hgA hgf hfg]; constructor=>//.
exact: norm_spaces_isomorphic_symmetric hS.
Qed.

(** Source for [norm_diffeomorphism_image]: the prescribed image is
    exactly f(A), supporting the definition in Federer 3.1.18, p. 229. *)
Lemma norm_diffeomorphism_image (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (B : set Y) (f : X->Y) (g : Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k -> f @` A=B.
Proof.
move=>hD; apply/seteqP; split=>y.
- move=>[x hx <-]; exact (@norm_diffeomorphism_maps R X Y NX NY hNX hNY A B f g k hD x hx).
- move=>hy; exists (g y); first exact (@norm_diffeomorphism_inverse_maps R X Y NX NY hNX hNY A B f g k hD y hy).
  exact (@norm_diffeomorphism_right_inverse R X Y NX NY hNX hNY A B f g k hD y hy).
Qed.

(** Source for [norm_diffeomorphism_source_open]: the open domain of
    a diffeomorphism, Federer 3.1.18, p. 229. *)
Lemma norm_diffeomorphism_source_open (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (B : set Y) (f : X->Y) (g : Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  @open [the topologicalType of real_norm_metric_space hNX] A.
Proof.
move=>hD.
exact (@norm_class_zero_domain_open R X Y NX NY hNX A f
  (@norm_class_continuous R X Y NX NY hNX hNY A f k (norm_diffeomorphism_forward_class hD))).
Qed.

(** Source for [norm_diffeomorphism_target_open]: the open image of
    a diffeomorphism, Federer 3.1.18, p. 229. *)
Lemma norm_diffeomorphism_target_open (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : set X) (B : set Y) (f : X->Y) (g : Y->X) k :
  is_norm_diffeomorphism hNX hNY A B f g k ->
  @open [the topologicalType of real_norm_metric_space hNY] B.
Proof. move=>hD; exact: norm_diffeomorphism_source_open (norm_diffeomorphism_symmetric hD). Qed.
